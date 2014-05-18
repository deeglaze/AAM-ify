#lang racket/base

#|
This module is a proof of concept that the allocation function and abstract abstract machine
for a semantics in a restricted language can be partially automatically generated from
the declarations of state spaces and reduction rules.

The key ideas:
* use graphs algorithms to find recursive mentions of a space to change out with Addr
* Spaces that are either a single map or are in their own SCC without self-reference
  are treated as "aliases" rather than have their names be implicitly μ-bound.
  This allows closures to have their environments' codomain be store-allocated rather than
  the whole environment itself.
* reduction relation can strongly update non-store functions (they will be made finite)
  maps with an abstract domain need cardinality analysis to do strong updates
* all store updates are made weak
* all store lookups are made non-deterministic
* Recursive data structure construction sites are noted to inform alloc which addresses to create.

FIXME: when a map is in a space that "later" needs a store lookup, how do we represent that?
|#

(require racket/unsafe/ops racket/set racket/match racket/list
         racket/trace
         racket/fixnum
         (only-in racket/bool implies)
         "spaces.rkt" "space-ops.rkt"
         "shared.rkt"
         "transform-language.rkt")
(provide abstract-rule
         abstract-meta-function)
(define-syntax-rule (matches? v pats ...) (match v [pats #t] ... [_ #f]))

;; expecting a component
(define (resolve-space-runtime spaces c name-within)
  (let go ([c c])
   (match c
     [(? Space-reference?) (go (hash-ref spaces (Space-reference-name c)))]
     [(User-Space C _ _) (go C)]
     [(? Variant?) (and (eq? name-within (Variant-name c)) c)]
     [(∪ _ Cs) (for/or ([c (in-list Cs)]) (go c))]
     [(or (? ℘?) (? Map?) (? terminal-component?) (? External-Space?)) #f]
     [_ (error 'resolve-space-runtime "Bad component ~a" c)])))

;; FIXME: all variants need to have their vpointers updated to the abstract language's.

;; Any deep pattern that recurs through an address gets turned into a non-deterministic match.
;; That is, if we have a pattern (say Pat) in a recursive position,
;;  - we create a fresh Name (say B) and
;;  - add a binding to the rule (Binding Pat (Choose (Store-lookup (Term (Rvar B)))))
;;  - Repeat the process for Pat.
(define (emit-binding-sc abs-lang pat caddr expected)
  (define new-bvar (gensym))
  (if (variant? pat)
      (let-values ([(pat* binding-scs si) (flatten-pattern abs-lang pat expected)])
        (values (Name new-bvar -Anything) ;; An address
                (cons (Binding pat*
                               (Choose read/many no-comp-yet caddr
                                       (Store-lookup reads no-comp-yet
                                                     (Term pure no-comp-yet (Rvar new-bvar)))))
                      binding-scs)
                (combine reads many si)))
      (values (Name new-bvar -Anything) ;; An address
              (list (Binding pat
                             (Choose read/many caddr no-comp-yet
                                     (Store-lookup reads no-comp-yet
                                                   (Term pure no-comp-yet (Rvar new-bvar))))))
              read/many)))

;; flatten-pattern : Pattern Option[Set[List[Component-Address]]] → (values Pattern List[Binding-side-conditions])
(define (flatten-pattern abs-lang pat expected)
  (match-define (Abs-Language (Language spaces _ options) rec-addrs
                              recursive-spaces _ nonrec-spaces) abs-lang)
  (define rrm
    (replace-recursive-mentions
     ;; we don't know the current space, thus #f
     options nonrec-spaces recursive-spaces #f))
  (define (flatten pat rev-addr expected rec-positions)
    (define (filter-by head [rec-positions rec-positions])
      (and rec-positions
           (for/set ([pos (in-set rec-positions)]
                     #:when (matches? pos (cons (== head equal?) rest)))
             pos)))

    (define raddr (and rec-positions (reverse rev-addr)))
    (cond [(and raddr
                (set-member? rec-positions raddr)
                (implies (Space-reference? expected)
                         (not (set-member? nonrec-spaces (Space-reference-name expected)))))
           (emit-binding-sc abs-lang pat raddr expected)]
          [else
           (match pat
             [(variant (and v (Variant _ name comps _ _)) pats)
              (define ecomps
                (match (resolve-space-runtime spaces expected name)
                  [(Variant _ _ comps _ _) comps]
                  [#f (for/vector #:length (vector-length comps)
                                  ([c (in-vector comps)])
                                  (rrm c))]
                  [_ (error 'flatten-pattern
                            "INTERNAL: typechecking should ensure expectations (~a) agree with reality (~a)"
                            expected v)]))
              ;; Trusted spaces' variants are all given an empty set of recursive references.
              (define rec-positions (hash-ref rec-addrs name ∅))
              (define pats* (make-vector (vector-length pats)))
              ;; OPT-OP: consider an RRB-tree for binding-scs if it's a bottleneck.
              (define-values (binding-scs* si*)
                (for/fold ([binding-scs '()]
                           [si pure])
                    ([pat (in-vector pats)]
                     [comp (in-vector ecomps)]
                     [i (in-naturals)])
                  (define addr (Variant-field name i))
                  ;; Filter out recursive positions that do not include the current field.
                  (define indexed-addresses (filter-by addr rec-positions))
                  (define-values (pat* binding-scs* si*)
                    (flatten pat (list addr) comp indexed-addresses))
                  (unsafe-vector-set! pats* i pat*)
                  (values (append (reverse binding-scs*) binding-scs)
                          (combine si si*))))
              (values (variant v pats*)
                      (reverse binding-scs*)
                      si*)]

             [(Name x pat)
              (define-values (pat* bscs* si*)
                (flatten pat rev-addr expected rec-positions))
              (values (Name x pat*) bscs* si*)]

             [(Map-with kpat vpat mpat mode (and mcomp (Map pc ex? kcomp vcomp)))
              (define-values (kpat* kbscs* ksi*)
                (flatten kpat (cons 'domain rev-addr) kcomp (filter-by 'domain)))
              (define-values (vpat* vbscs* vsi*)
                (flatten vpat (cons 'range rev-addr) vcomp (filter-by 'range)))
              (define-values (mpat* mbscs* msi*)
                (flatten mpat rev-addr mcomp rec-positions))
              (values (Map-with kpat* vpat* mpat* mode
                                (Map #f #f (rrm kcomp) (rrm vcomp)))
                      (append kbscs* vbscs* mbscs*)
                      (combine ksi* vsi* msi*))]
             [(Set-with vpat spat mode (and scomp (℘ pc ex? comp)))
              (define-values (vpat* vbscs* vsi*)
                (flatten vpat (cons '℘ rev-addr) comp (filter-by '℘)))
              (define-values (spat* sbscs* ssi*)
                (flatten spat rev-addr scomp rec-positions))
              (values (Set-with vpat* spat* mode (℘ #f #f (rrm comp)))
                      (append vbscs* sbscs*)
                      (combine vsi* ssi*))]

             [(Rvar x) (error 'flatten-pattern "Unexpected reference in match pattern ~a" x)]
             ;; XXX: good?
             [other (values other '() pure)])]))
  (flatten pat '() expected #f))

;; TODO: this function now needs to also produce the component that we should expect.
(define (check-and-rewrite-term options rec-addrs alloc-tag tm relabeling)
  ;; if current position is recursive, hoist pattern out into allocation+store-update.
  ;; Hoist inside-out in order to do it in one pass.
  (define (recur current-variant rev-addr rev-local-addr tm)
    (define rec-addresses
      (if current-variant
          (hash-ref rec-addrs current-variant ∅)
          ∅))
    (cond
     [(set-member? rec-addresses (reverse rev-local-addr))
      (define address-var (gensym))
      (define-values (pat* store-updates susi)
        (recur #f rev-addr '() tm))
      (define mb
        (or (Options-match-default options)
            core-match-default))
      (define eb
        (or (Options-equal-default options)
            core-equal-default))
      (define Acomp (Address-Space 'AAM mb eb))
      (define hint (cons alloc-tag (reverse rev-addr)))
      (define hint* (hash-ref relabeling hint hint))
      (values (Rvar address-var)
              (append
               store-updates
               (list (Binding (Name address-var -Anything)
                              (Alloc allocs Acomp 'AAM mb eb hint*))
                     (Store-extend (Term pure Acomp (Rvar address-var))
                                   (Term pure no-comp-yet pat*)
                                   #f)))
              (combine writes allocs susi))]
     [else
      (match tm
        [(or (? is-a?) (? Name?) (? Map-with?) (? Set-with?))
         (error 'abstract-rule "Rule RHS may not bind or match ~a" tm)]
        [(variant (and v (Variant _ name _ trust-recursion? trust-construction?)) pats)
         ;; TODO: update to use with-orig-stx and raise syntax error.
         (unless (implies trust-recursion? trust-construction?)
           (error 'check-and-rewrite-term
                  "Variant in trusted recursive space does not have trusted construction: ~a" tm))
         ;; When recursive and trusted, do not rewrite positions,
         ;; but subterms without trust must be rewritten.
         ;; When "current-variant" is #f, then nothing is rewritten.
         (define checked-variant-name
           (and (not trust-recursion?) name))
         (define len (vector-length pats))
         (define pats* (make-vector len))
         (define-values (rev-store-updates susi)
          (for/fold ([rev-store-updates '()]
                     [susi pure])
               ([pat (in-vector pats)]
                [i (in-naturals)])
             (define vfield (Variant-field name i))
             (define-values (pat* store-updates* susi*)
               (recur checked-variant-name
                      (cons vfield rev-addr)
                      (list vfield)
                      pat))
             (unsafe-vector-set! pats* i pat*)
             (values
              (append (reverse store-updates*) rev-store-updates)
              (combine susi susi*))))
         (values (variant v pats*) (reverse rev-store-updates) susi)]
        ;; XXX: is this the right thing? Anything else here?
        [other (values other '() pure)])]))
  (recur #f '() '() tm))

(define (abstract-meta-function abs-lang ΞΔ relabeling mf #:options [options #f])
  (match-define (Meta-function name rules si t/conc t/abs) mf)
  (cond
   [t/abs mf]
   [else
    (define-values (rev-rules* si)
      (for/fold ([rrules '()] [si pure]) ([rule (in-list rules)]
                                          [i (in-naturals)])
        (define r (abstract-rule abs-lang ΞΔ rule i relabeling
                                 #:path (list name)
                                 #:options options))
        (values (cons r rrules) (combine si r))))
    (Meta-function name (reverse rev-rules*) si t/conc #f)]))

;; abstract-rule
(define (abstract-rule abs-lang ΞΔ rule rule-number relabeling
                       #:path [path '()]
                       #:options [options #f])
  (match-define
   (Abs-Language (Language spaces _ loptions) rec-addrs rec-spaces _ nonrec-spaces) abs-lang)
  (match-define (Rule rule-name lhs rhs (BSCS si binding-side-conditions) lexpect rexpect) rule)

  ;; Now we rewrite the LHS to non-deterministically choose values when it
  ;; pattern matches on recursive positions.
  ;; FIXME: Space patterns not replaced with their transformed versions.
  (define-values (lhs* lhs-binding-side-conditions lsi)
    (flatten-pattern abs-lang lhs lexpect))

  (define rule-tag (or rule-name `(Rule ,rule-number)))

  ;; Finally we rewrite the binding side-conditions to go between the
  ;; lhs and rhs bindings/side-conditions
  (match-define (BSCS bscssi binding-side-conditions*)
                (abstract-bindings abs-lang ΞΔ relabeling
                                   (cons rule-tag path)
                                   binding-side-conditions
                                   (λ (bscs* si)
                                      (BSCS (combine lsi si) bscs*))
                                   #:options options))

  ;; We now need to flatten the lhs pattern, and all patterns in binding-side-conditions.
  ;; The RHS pattern needs its recursive positions replaced with allocated addresses and
  ;; corresponding weak updates to the store.

  ;; First we check that no trusted recursive spaces have any variants constructed in rhs.
  (define-values (rhs* store-updates susi)
    (check-and-rewrite-term options rec-addrs (append path (list rule-tag 'RHS)) rhs relabeling))

  (define bscs* (append lhs-binding-side-conditions
                        binding-side-conditions*
                        store-updates))
  (define rrm (replace-recursive-mentions loptions nonrec-spaces rec-spaces #f))
  (define lexpect* (and lexpect (rrm lexpect)))
  (define rexpect* (and rexpect (rrm rexpect)))
  (Rule rule-name lhs* rhs* (BSCS (combine bscssi susi) bscs*)
        lexpect* rexpect*))

(define (abstract-bindings abs-lang ΞΔ relabeling rev-addr bscs kont #:options [options #f])
  (let let-recur ([bindings bscs] [i 0] [bindings* '()] [susi pure])
    (match bindings
      ['() (kont (reverse bindings*) susi)]
      [(cons binding bindings)
       (define (continue bindings* si)
         (let-recur bindings (add1 i) bindings* (combine si susi)))
       (match binding
         [(Binding pat expr)
          (define-values (pat* bscs-for-pat* si*)
            (flatten-pattern abs-lang pat (expression-comp expr)))
          (define e* (abstract-expression* abs-lang ΞΔ relabeling expr
                                           (cons `(Let-binding ,i) rev-addr)
                                           #:options options))
          (continue (append (reverse (cons (Binding pat* e*) bscs-for-pat*))
                            bindings*)
                    (combine si* e*))]
         [(Store-extend kexpr vexpr trust-strong?)
          (define k* (abstract-expression* abs-lang ΞΔ relabeling kexpr
                                           (cons `(Let-store-key ,i) rev-addr)
                                           #:options options))
          (define v* (abstract-expression* abs-lang ΞΔ relabeling vexpr
                                           (cons `(Let-store-val ,i) rev-addr)
                                           #:options options))
          (continue (cons (Store-extend k* v* trust-strong?) bindings*)
                    (combine writes k* v*))]
         [(When expr)
          (define w* (abstract-expression* abs-lang ΞΔ relabeling expr
                                           (cons `(When-expr ,i) rev-addr)
                                           #:options options))
          (continue (cons (When w*) bindings*)
                    (expression-store-interaction w*))])])))
;; abstract-expression
;; An EPattern must be abstracted so that Term expressions are rewritten and
;; stores are threaded through meta-function-call's.
;; After this, the binders in the LHS pattern get chosen from the abstract positions like in rules.
;; OPT-OP (ΞΔ): do analysis on meta-functions first to determine if they need to produce new stores,
;;              then only meta-function-call's that produce new stores get marked as changing store.
(define (abstract-expression abs-lang ΞΔ relabeling alloc-tag expr #:options [options #f])
  (abstract-expression* abs-lang ΞΔ relabeling expr (list alloc-tag) #:options options))

;; FIXME?: double check store-interactions
(define (abstract-expression* abs-lang ΞΔ relabeling expr rev-addr #:options [options #f])
  (define rec-addrs (Abs-Language-recursive-addresses abs-lang))
  (define (bind expr path fn [name #f])
    (define e* (abstract-expression* abs-lang ΞΔ relabeling expr path #:options options))
    (cond
     [(writes? (combine e*))
      (define var (if name (gensym name) (gensym 'intermediate)))
      (define r (fn (Term pure no-comp-yet (Rvar var))))
      (Let (combine e* r)
           (BSCS (combine e*) (list (Binding (Name var -Anything) e*)))
           r)]
     [else (fn e*)]))

  (define (binary e₀ e₁ tag₀ tag₁ container [name₀ #f] [name₁ #f])
    (bind e₀ (cons tag₀ rev-addr)
          (λ (e₀*)
             (bind e₁ (cons tag₁ rev-addr)
                   (λ (e₁*) (container (combine e₀* e₁*) e₀* e₁*))
                   name₁))
          name₀))

  (define (recur expr rev-addr)
    (match expr
     [(Term _ _ pattern)
      ;; We use the path taken to this expr as the tag for allocation.
      (define-values (pat* store-updates si)
        (check-and-rewrite-term options rec-addrs (reverse rev-addr) pattern relabeling))
      ;; If no store updates, then no new store.
      (cond
       [(empty? store-updates) (Term pure no-comp-yet pat*)]
       [else (Let si no-comp-yet (BSCS si store-updates) (Term pure no-comp-yet pat*))])]

     [(Store-lookup _ _ kexpr)
      (bind kexpr
            (cons 'SL-key rev-addr)
            (λ (k*)
               (define slsi (combine reads k*))
               ;; TODO: use type of kexpr to guide choose lookup or not.
               (Choose (add-many slsi) no-comp-yet (gensym) (Store-lookup slsi no-comp-yet k*)))
            'key)]

     [(Meta-function-call _ _ name arg-pat)
      (define-values (pat* store-updates si)
        (check-and-rewrite-term options rec-addrs (reverse rev-addr) arg-pat relabeling))
      (define mfsi (hash-ref ΞΔ name read/write/alloc/many))
      (cond [(empty? store-updates)
             (Meta-function-call mfsi no-comp-yet name pat*)]
            [else (Let si (BSCS si store-updates)
                       (Meta-function-call mfsi no-comp-yet name pat*))])]

     [(If _ _ g t e)
      (bind g
            (cons 'If-guard rev-addr)
            (λ (g*)
               (define t* (recur t (cons 'If-then rev-addr)))
               (define e* (recur e (cons 'If-else rev-addr)))
               (If (combine g* t* e*) no-comp-yet g* t* e*)))]

     [(Equal _ c lexpr rexpr)
      (binary lexpr rexpr 'Equal-left 'Equal-right
              (λ (si l* r*) (Equal (add-many si) c l* r*)))]

     ;; Let is tricky since it might have rebindings of the store, which need to be forwarded as the
     ;; next store when translation goes forward.

     [(Let _ _ (BSCS _ bindings) body)
      ;; In order to not get generated lets in let clauses,
      ;; we bind Binding RHSs to variables that then get matched against their pattern.
      (abstract-bindings
       abs-lang ΞΔ relabeling rev-addr bindings
       (λ (bindings* susi)
          (cond
           [(empty? bindings*) (recur body rev-addr)]
           [else
            (bind body
                  (cons 'Let-body rev-addr)
                  (λ (b*)
                     (Let (combine susi b*)
                          (expression-comp b*)
                          (BSCS susi bindings*)
                          b*)))]))
       #:options options)]

     [(Match _ _ dexpr rules)
      (bind dexpr
            (cons 'Match-discriminant rev-addr)
            (λ (d*)
               (define rules*
                 (for/list ([rule (in-list rules)]
                            [i (in-naturals)])
                   (abstract-rule abs-lang ΞΔ rule i
                                  relabeling
                                  #:path (cons 'Match-rule rev-addr)
                                  #:options options)))
               (Match (combine d* (apply combine rules*))
                      no-comp-yet
                      d* rules*)))]

     [(Choose _ _ ℓ cexpr)
      (bind cexpr
            (cons 'Choose-expr rev-addr)
            (λ (ec*) (Choose (combine many ec*)
                             (match (expression-comp ec*)
                               [(℘ _ _ c) c]
                               [_ #f])
                             ℓ ec*)))]

;;; Map operations

     [(Map-lookup _ _ m kexpr default? dexpr)
      (bind kexpr
            (cons 'ML-key rev-addr)
            (λ (k*)
               (cond
                [default?
                  (bind dexpr
                        (cons 'ML-default rev-addr)
                        (λ (d*)
                           (Map-lookup (combine k* d*) no-comp-yet m k* #t d*))
                        'default)]
                [else (Map-lookup (combine k*) no-comp-yet m k* #f #f)]))
            'key)]

     [(Map-extend _ _ m kexpr vexpr trust-strong?)
      (binary kexpr vexpr 'ME-key 'ME-val
              (λ (si k* v*) (Map-extend si no-comp-yet m k* v* trust-strong?)) 'key)]

     [(Map-remove _ _ mvar kexpr)
      (bind kexpr
            (cons 'Map-remove-key rev-addr)
            (λ (k*) (Map-remove (combine many k*) no-comp-yet mvar k*)))]

     [(In-Dom? _ c mvar kexpr)
      (bind kexpr
            (cons 'In-Dom?-key rev-addr)
            (λ (k*) (In-Dom? (combine many k*) c mvar k*)))]

;;; Set operations

     [(or (Set-Add* _ _ sexpr vexprs)
          (Set-Remove* _ _ sexpr vexprs)
          (Set-Intersect _ _ sexpr vexprs)
          (Set-Union _ _ sexpr vexprs)
          (Set-Subtract _ _ sexpr vexprs))
      (define container
        (cond [(Set-Add*? expr) Set-Add*]
              [(Set-Union? expr) Set-Union]
              [(Set-Remove*? expr) Set-Remove*]
              [(Set-Intersect? expr) Set-Intersect]
              [(Set-Subtract? expr) Set-Subtract]))
      (define base (object-name container))
      (define-values (base-tag arg-tag)
        (values (string->symbol (format "~a-set" base))
                (string->symbol (format "~a-val" base))))
      (if (empty? vexprs)
          (recur sexpr rev-addr)
          (bind sexpr
                (cons base-tag rev-addr)
                (λ (s*)
                   (let set-op-recur ([vexprs vexprs] [i 0] [vexprs* '()] [si pure])
                     (match vexprs
                       ['() (container si no-comp-yet s* (reverse vexprs*))]
                       [(cons v vexprs)
                        (bind v
                              (cons (list arg-tag i) rev-addr)
                              (λ (v*)
                                 (set-op-recur vexprs (add1 i) (cons v* vexprs*)
                                               (combine si v*))))])))))]

     [(In-Set? _ c sexpr vexpr)
      (binary sexpr vexpr 'In-Set?-set 'In-Set?-value
              (λ (si s* v*) (In-Set? (add-many si) c s* v*)))]

     [(Set-empty? _ c sexpr)
      (bind sexpr
            (cons 'Set-empty-val rev-addr)
            (λ (s*) (Set-empty? (combine many s*) c s*)))]

     [(Alloc _ c space mb eb hint)
      (define hint* (if (eq? hint -unmapped)
                        (reverse rev-addr)
                        hint))
      (define rehint (hash-ref relabeling hint* hint*))
      (Alloc allocs c space mb eb rehint)]

     [(or (? Unsafe-store-ref?) (? Unsafe-store-space-ref?)
          (? Map-empty??) (? Empty-set?) (? Empty-map?) (? ????))
      expr]
     [_ (error 'abstract-expression "Bad expression ~a" expr)]))
  (recur expr rev-addr))
