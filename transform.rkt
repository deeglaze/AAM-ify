#lang racket

#|
This module is a proof of concept that the allocation function and abstract abstract machine
for a semantics in a restricted language can be partially automatically generated from
the declarations of state spaces and reduction rules.

The key ideas:
* use graphs algorithms to find recursive mentions of a space to change out with Addr
* reduction relation can strongly update non-store functions (they will be made finite)
  maps with an abstract domain need cardinality analysis to do strong updates
* all store updates are made weak
* all store lookups are made non-deterministic
* Recursive data structure construction sites are counted to inform alloc how many addresses to create.
* ASSUMPTION: distinct addresses are desired for these syntactically distinct allocation points.

|#

(require graph
         racket/unsafe/ops
         racket/trace
         racket/fixnum
         "spaces.rkt"
         "shared.rkt")
(provide abstract-language
         abstract-rule
         abstract-meta-function)

;; language->graph : Language → unweighted-directed-graph
(define (language-spaces->graph spaces)
  (define LG (unweighted-graph/directed '()))
  (define Space-nodes (add-space-nodes! LG spaces))
  (for ([(name space) (in-dict spaces)])
    (add-space-edges! LG Space-nodes name space))
  LG)

;; An Endpoint is an (Endpoint Variant-Address Space-Name)
(struct Endpoint (address space) #:transparent)
(struct Space-node (name trust-rec trust-con) #:transparent)
;; distinguish space from reference to identify recursive spaces
(struct Space-ref-node (sn) #:transparent)

;; Spaces are represented as Pair[Space-name,Trusted?] to do error-checking.
;; If two spaces with different trusted? booleans appear in the same scc, error.
(define (add-space-nodes! G spaces)
  (for/fold ([h ρ₀]) ([(name space) (in-dict spaces)])
    (hash-set h name
              (match space
                [(or (? Address-Space?) (? External-Space?))
                 (unless (has-vertex? G space) (add-vertex! G space))
                 space]
                [(User-Space variants trust-recursion? trust-construction?)
                 (define node (Space-node name trust-recursion? trust-construction?))
                 (define self-node (Space-ref-node node))
                 (unless (has-vertex? G node)
                   (add-vertex! G node)
                   (add-vertex! G self-node)
                   (add-directed-edge! G self-node node))
                 node]))))

(define (add-space-edges! G Space-nodes name space)
  (match space
    [(User-Space variants-or-components trust-recursion? trust-construction?)
     (define node (hash-ref Space-nodes name))
     (for* ([variant-or-component (in-list variants-or-components)]
            [endpoint (in-set (variant-or-component->endpoints name variant-or-component))])
       (match-define (Endpoint addr space) endpoint)
       (define space-node
         (if (Address-Space? space)
             space
             (match (hash-ref Space-nodes space
                        (λ () (error 'add-space-edges!
                                     "Space ~a refers to unknown space ~a" name space)))
               [(? Space-node? sn) (Space-ref-node sn)]
               [other other])))
       (add-directed-edge! G node addr)
       (add-directed-edge! G addr space-node))]
    [_ (void)]))

;; language-recursive-spaces : Map[Space-name,Space] → Map[Space-name,Set[Space-Name]]
;; Map space names to set of space names that are mutually recursive with them.
;; Examples: List[A] = nil | (Cons A List[A]) ==> 'List |-> (set 'List)
;;           S-exp[A] = A | S-exps[A]
;;           S-exps[A] = nil | (Cons S-exp[A] S-exps[A]) ==> ['S-exp |-> #0=(set 'S-exp 'S-exps), 'S-exps |-> #0#]
;; NOTE: a space without Variants is not recursive since the recursion gets externalized.
(define (language-recursive-spaces spaces)
  (define LG (language-spaces->graph spaces))
  ;; Do a little error checking while discovering recursion.
  (define recursive-islands (scc LG))
  (define (external-recursion? name)
    (match (hash-ref spaces name)
      [(or (? Address-Space?) (? External-Space?)) #t]
      [(User-Space v-or-cs _ _)
       (not (for/or ([v-or-c (in-list v-or-cs)]) (Variant? v-or-c)))]))
  ;; Make a map of Space-name to Set[spaces recursive with Space]
  (for/fold ([h ρ₀]) ([cc (in-list recursive-islands)]
                      #:unless (match cc
                                 ;; The reference nodes themselves are administrative.
                                 [(list (? Space-ref-node?)) #t] [_ #f]))
      (define spaces
        (for/set ([c (in-list cc)] #:when (Space-ref-node? c)) (Space-ref-node-sn c)))
      (define space-names
        (for/set ([space (in-set spaces)]) (Space-node-name space)))
      (define-values (h* dummy0 dummy1)
       (for/fold ([h h] [trust-rec 'unspecified] [trust-con 'unspecified])
           ([space (in-set spaces)])
         (match-define (Space-node _ ctrust-rec ctrust-con) space)
         (cond [(and (or (eq? trust-rec 'unspecified) (equal? trust-rec ctrust-rec))
                     (or (eq? trust-con 'unspecified) (equal? trust-con ctrust-con)))
                (define name (Space-node-name space))
                (values (if (external-recursion? name)
                            h
                            (hash-set h name space-names))
                        ctrust-rec
                        ctrust-con)]
               [else
                (error 'bad-trust "Recursive spaces have mismatched recursion trust ~a" cc)])))
      h*))

(define (language-abstract-spaces-and-recursive-positions spaces recursive-spaces)
  ;; Seed the abstract space map with defaults we know.
  (define abstract-spaces₀
    (for/fold ([h ρ₀]) ([(name space) (in-dict spaces)])
      (match space
        [(External-Space _ _ precision _)
         (hash-set h name (not (eq? precision 'concrete)))]
        [(Address-Space space)
         (hash-set h name #t)]
        [(User-Space _ trust-recursion? trust-construction?)
         (hash-set h name (if trust-recursion? #f ∅))])))

  ;; Find all recursive addresses and build the first pass of abstract-spaces.
  (define-values (variant-rec-addrs abstract-spaces₁)
    (for/fold ([rec-addrs ρ₀] [abstract-spaces abstract-spaces₀])
        ([(name space) (in-dict spaces)])
      
      (match space
        [(or (? External-Space?) (? Address-Space?)) (values rec-addrs abstract-spaces)]
        [(User-Space variants-or-components trust-recursion? trust-construction?)
         (cond
          [trust-recursion?
           ;; All variants are mapped to ∅ to drive later "recursive replacements" to leave
           ;; trusted spaces alone.
           (values
            (for/fold ([rec-addrs rec-addrs]) ([v/c (in-list variants-or-components)]
                                               #:when (Variant? v/c))
              (hash-set rec-addrs (Variant-name v/c) ∅))
            abstract-spaces)]
          [else
           ;; update rec-addrs and abs-spaces for each variant/component in the space.
           (for/fold ([rec-addrs rec-addrs]
                      [abs-spaces abstract-spaces])
               ([variant-or-component (in-list variants-or-components)])
             (find-recursive-mentions recursive-spaces
                                      name
                                      variant-or-component
                                      rec-addrs
                                      abs-spaces))])])))

  ;; All spaces should now be classified as abstract or not.
  (define abstract-spaces
    (for/fold ([h abstract-spaces₁]) ([name (in-hash-keys abstract-spaces₁)])
      (search-space-abstract h name)))
  (values abstract-spaces variant-rec-addrs))

;; abstract-language : Language →
;; (values Language
;;         Map[Variant-name,Set[Variant-Address]]
;;         Map[Space-name,Boolean]
;;         Variant-name)
;;
;; Returns (1) a language that cuts all recursion out into addresses,
;; (2) a map from variants to positions of self-reference (and mutually-recursive references),
;; (3) a map from space names to whether or not they are "abstract,"
;; (4) a fresh variant name for packaging up intermediate terms with updated stores.
(define (abstract-language L)
  ;; We first turn L into a graph in the following way:
  ;; External spaces and (Address-Space) are terminal nodes (no outgoing edges).
  ;; Space names are nodes that point to all of their variant nodes' Variant-Addresses
  ;; (Space-reference name) is treated as the node for name.

  ;; All space names (S) that are in the same strongly connected component are treated as
  ;; recursive. That is, for the Variants-or-Components in S, any (Space-reference name) is
  ;; replaced by (Address-Space) when name ∈ S, and the address of the position is added to
  ;; the recursive mention map.

  (match-define (Language spaces refinement-order) L)
  (define recursive-spaces (language-recursive-spaces spaces))
  (define-values (abstract-spaces variant-rec-addrs)
    (language-abstract-spaces-and-recursive-positions spaces recursive-spaces))

  (printf "Recursive spaces ~a~%" recursive-spaces)

  ;; replace-recursive-mentions : Space-name (∪ Variant Component) → (∪ Variant Component)
  ;; With abstract spaces and recursive spaces computed, we can lift abstract maps to powerset codomain,
  ;; and replace spaces in recursive positions with (Address-Space)
  (define (replace-recursive-mentions current-space variant-or-component)
    ;; replace-recursive-mentions-in-component :
    ;;  Component → (values Component Boolean)
    ;; The boolean is #t if any component is abstracted, including non-recursive space references
    ;; to spaces that have been rewritten to be abstract.
    ;; This "including" clause is tricky, since we're in the middle of abstracting all the spaces.
    (define (replace-recursive-mentions-in-component comp)
      (match comp
        [(Space-reference name)
         (if (set-member? (hash-ref recursive-spaces current-space ∅) name)
             (values (Address-Space 'AAM) #t)
             ;; Non-recursive references are not replaced, even if the spaces are abstract.
             (values comp
                     (hash-ref abstract-spaces name
                               (λ () (error 'replace-component "Impossible")))))]
        [(℘ comp) (replace-recursive-mentions-in-component comp)]
        [(or (Map domain range)
             ;; Fix qualification if one given.
             (QMap domain _ range))
         (define-values (abs-dom dom-abs?)
           (replace-recursive-mentions-in-component domain))
         (define-values (abs-range rng-abs?)
           (replace-recursive-mentions-in-component range))
         ;; If a map domain contains addresses, the map is now treated as
         ;; m(a) = b implies ∃ A ∈ γ(a). A ↦ b, but we don't know if A is actually in the map.
         ;; Additionally, the Map now becomes weak, so b is lifted implicitly to a powerset domain.
         (cond [dom-abs? (values (QMap abs-dom #t (℘ abs-range)) #t)]
               [else (values (QMap abs-dom #f abs-range) rng-abs?)])]

        [(Address-Space _) (values comp #t)]))
    (trace replace-recursive-mentions-in-component)

    (match variant-or-component
      [(Variant name comps tr tc)
       (define abs-comps
         (for/vector #:length (vector-length comps)
                     ([comp (in-vector comps)])
           (define-values (abs-comp dummy)
             (replace-recursive-mentions-in-component comp))
           abs-comp))
       (Variant name abs-comps tr tc)]
      [comp
       (define-values (abs-comp dummy)
         (replace-recursive-mentions-in-component comp))
       abs-comp]))
  (trace replace-recursive-mentions)

   ;; Now replace recursive references with Address-Space and build a
   ;; Map[Variant-name,Set[Variant-address]] where the set is all the addresses of the
   ;; recursive positions.
   (define abs-spaces
     (for/fold ([abs-spaces ρ₀])
         ([(name space) (in-dict spaces)])
       (define abs-space
         (match space
           [(or (? External-Space?) (? Address-Space?))
            space]

           [(User-Space variants trust-recursion? trust-construction?)
            (define abs-variants
              (for/list ([variant (in-list variants)])
                (replace-recursive-mentions name variant)))

            ;; If recursion is trusted, don't give rewritten form.
            ;; We just did that to get the recursive addresses.
            ;; FIXME: is doing this necessary at all if trust-recursion?
            (if trust-recursion?
                space
                (User-Space abs-variants trust-recursion? trust-construction?))]))

       (hash-set abs-spaces name abs-space)))

   (values (Language abs-spaces refinement-order)
           variant-rec-addrs
           abstract-spaces))

;; find-recursive-mentions :
;;  Map[Space-name,Set[Space-name]] Space-name (∪ Variant Component) Map[Variant-name,Variant-Address] Rec-Space-Map →
;;    (values Map[Variant-name,Variant-Address] Rec-Space-Map)
;; Where Rec-Space-Map = Map[Space-name,(∪ Set[Space-name] Boolean)]
;; Purpose:
;; Build a map of Variant name to addresses of recursive space references,
;; and a map of Space-name to Boolean (abstracted or not?) or a union of spaces of which, if abstract,
;; makes the key space abstract. All mutual dependencies are trusted, making the spaces non-abstract.
(define (find-recursive-mentions recursive-spaces
                                 current-space
                                 variant-or-component
                                 rec-addrs
                                 abs-spaces)
  (define (hash-set-if-unresolved h k v)
    (match (hash-ref h k -unmapped)
      [(? boolean?) h]
      [_ (hash-set h k v)]))
  ;; Get the set of recursive mentions and fill out abstract-space dependencies.
  (define (find-recursive-mentions-in-component comp rev-addr abs-spaces)
    (match comp
      [(Space-reference name)
       (cond
        [(set-member? (hash-ref recursive-spaces current-space ∅) name)
         (values (set (reverse rev-addr))
                 (hash-set-if-unresolved abs-spaces current-space #t))]
        [else
         (values ∅
          (match (hash-ref abs-spaces name ∅)
            [#t ;; known recursive (already set if trusted)
             (hash-set-if-unresolved abs-spaces current-space #t)]
            [#f abs-spaces] ;; known non-recursive
            ;; unknown. Add to set of names to resolve after finishing.
            [dependents
             (cond
              [(boolean? (hash-ref abs-spaces current-space -unmapped))
               ;; Already showed current-space is abstract for a different reason.
               ;; We don't know more about name here.
               abs-spaces]
              [(set? dependents)
               ;; If name is abstract, then so is current-space.
               (hash-join abs-spaces current-space (set-add dependents name))]
              [else (error 'find-recursive-mentions-in-component
                           "INTERNAL: expected boolean or set: ~v" dependents)])]))])]
      [(℘ comp)
       (find-recursive-mentions-in-component comp (cons '℘ rev-addr) abs-spaces)]
      [(Map domain range)
       (define-values (rec-addresses abs-spaces*)
         (find-recursive-mentions-in-component domain (cons 'domain rev-addr) abs-spaces))
       (define-values (rec-addresses* abs-spaces**)
         (find-recursive-mentions-in-component range (cons 'range rev-addr) abs-spaces*))
       (values (set-union rec-addresses rec-addresses*) abs-spaces**)]
      [(? Address-Space?) (values ∅ (hash-set abs-spaces current-space #t))]))

  (match variant-or-component
    [(Variant name comps tr tc)
     (for/fold ([rec-addrs* rec-addrs] [abs-spaces* abs-spaces])
         ([comp (in-vector comps)]
          [i (in-naturals)])
       (define-values (rec-addresses abs-spaces**)
         (find-recursive-mentions-in-component
          comp (list (Variant-field name i)) abs-spaces*))
       (values (hash-join rec-addrs* name rec-addresses)
               abs-spaces**))]
    [comp
     (define-values (rec-addresses abs-spaces*)
       (find-recursive-mentions-in-component comp '() abs-spaces))
     ;; A recursive mention not under a variant must be under a map.
     ;; Maps are ensured finite by the rest of the abstraction process.
     (values rec-addrs abs-spaces*)]))

;; Resolve any left-over dependencies for abstraction.
;; When backchaining, fill out table with intermediate results.
(define (search-space-abstract abs-spaces space-name)
  (define catch-self (mutable-set))
  (define-values (abs-spaces* dummy)
    (let loop ([abs-spaces abs-spaces] [space-name* space-name])
      (when (set-member? catch-self space-name*)
        (error 'search-space-abstract
               "INTERNAL: Uncaught recursion on ~a given ~a"
               space-name abs-spaces))
      (set-add! catch-self space-name*)
      (match (hash-ref abs-spaces space-name*)
        [(? boolean? b) (values abs-spaces b)]
        [deps
         (define-values (abs-spaces* b)
           (for/fold ([h abs-spaces] [b #f])
               ([dep (in-set deps)])
             (define-values (h* b*) (loop h dep))
             (values h* (or b* b))))
         (values (hash-set abs-spaces* space-name* b) b)])))
  abs-spaces*)

(define (component->endpoints comp)
  (let build ([comp comp] [rev-addr '()])
    (match comp
      [(Space-reference name) (set (Endpoint (reverse rev-addr) name))]
      [(℘ comp) (build comp (cons '℘ rev-addr))]
      [(Map domain range)
       (set-union (build domain (cons 'domain rev-addr))
                  (build range (cons 'range rev-addr)))]
      [(? Address-Space?) (set (Endpoint (reverse rev-addr) comp))]
      [_ (error 'component->endpoints "Bad component ~a" comp)])))

;; variant->endpoints : Variant → Set[Endpoint]
;; compute all Variant-Addresses to a terminal space name for a given variant.
(define (variant-or-component->endpoints name v)
  (match v
    [(Variant name comps tr tc)
     (for/fold ([acc ∅]) ([comp (in-vector comps)]
                          [i (in-naturals)])
       (for/fold ([acc acc]) ([endpoint (in-set (component->endpoints comp))])
         (match-define (Endpoint addr space) endpoint)
         (set-add acc (Endpoint (cons (Variant-field name i) addr) space))))]
    [comp (for/set ([endpoint (in-set (component->endpoints comp))])
            (match-define (Endpoint addr space) endpoint)
            (Endpoint (cons (Space-component name) addr) space))]))

;; Any deep pattern that recurs through an address gets turned into a non-deterministic match.
;; That is, if we have a pattern (say Pat) in a recursive position,
;;  - we create a fresh Name (say B) and
;;  - add a binding to the rule (Binding Pat (Choose (Store-lookup (Term (Rvar B)))))
;;  - Repeat the process for Pat.
(define (emit-binding-sc rec-addrs pat)
  (define new-bvar (gensym))
  (if (variant? pat)
      (let-values ([(pat* binding-scs si) (flatten-pattern rec-addrs pat '() #f)])
        (values (Name new-bvar (Space (Address-Space 'AAM)))
                (cons (Binding pat* (Choose read/many (gensym)
                                            (Store-lookup reads (Term pure (Rvar new-bvar)))))
                      binding-scs)
                (combine reads many si)))
      (values (Name new-bvar (Space (Address-Space 'AAM)))
              (list (Binding pat (Choose read/many (gensym)
                                         (Store-lookup reads (Term pure (Rvar new-bvar))))))
              read/many)))

;; flatten-pattern : Pattern Option[Set[List[Component-Address]]] → (values Pattern List[Binding-side-conditions])
(define (flatten-pattern rec-addrs pat rev-addr [rec-positions #f])
  (cond [(and rec-positions (set-member? rec-positions (reverse rev-addr)))
         (emit-binding-sc rec-addrs pat)]
        [else
         (match pat
           [(variant (and v (Variant name _ _ _)) pats)
            ;; Trusted spaces' variants are all given an empty set of recursive references.
            (define rec-positions (hash-ref rec-addrs name ∅))
            (define pats* (make-vector (vector-length pats)))
            ;; OPT-OP: consider an RRB-tree for binding-scs if it's a bottleneck.
            (define-values (binding-scs* si*)
              (for/fold ([binding-scs '()]
                         [si pure])
                  ([pat (in-vector pats)]
                   [i (in-naturals)])
                (define indexed-addresses
                  (for/set ([pos (in-set rec-positions)]
                            #:when (match pos
                                     [(cons (Variant-field (== name)
                                                           (== i equal?))
                                            rest) #t]
                                     [_ #f]))
                    pos))
                (define-values (pat* binding-scs* si*)
                  (flatten-pattern rec-addrs pat (list (Variant-field name i)) indexed-addresses))
                (unsafe-vector-set! pats* i pat*)
                (values (append (reverse binding-scs*) binding-scs)
                        (combine si si*))))
            (values (variant v pats*)
                    (reverse binding-scs*)
                    si*)]

           [(Name x pat)
            (define-values (pat* bscs* si*) (flatten-pattern rec-addrs pat rev-addr rec-positions))
            (values (Name x pat*) bscs* si*)]

           ;; FIXME: recursive addresses assume only variants, but now we have recursive maps.
           [(Map-with kpat vpat mpat mode)
            (define-values (kpat* kbscs* ksi*)
              (flatten-pattern rec-addrs kpat (cons 'domain rev-addr) rec-positions))
            (error 'flatten-pattern "TODO map-with")]
           [(Set-with vpat spat mode)
            (error 'flatten-pattern "TODO set-with")]

           [(Rvar x) (error 'flatten-pattern "Unexpected reference in match pattern ~a" x)]
           ;; XXX: good?
           [other (values other '() pure)])]))

(define (check-and-rewrite-term rec-addrs alloc-tag tm)
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
      (values (Rvar address-var)
              (append
               store-updates
               (list (Binding (Avar address-var)
                              (QSAlloc allocs 'AAM (cons alloc-tag (reverse rev-addr))))
                     (Store-extend (Term pure (Rvar address-var))
                                   (Term pure pat*)
                                   #f)))
              (combine writes allocs susi))]
     [else
      (match tm
        [(or (? Space?) (? Name?) (? Map-with?) (? Set-with?))
         (error 'abstract-rule "Rule RHS may not bind or match ~a" tm)]
        [(variant (and v (Variant name _ _ trust-construction?)) pats)
         ;; FIXME: update to use with-orig-stx and raise syntax error.
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

(define (abstract-meta-function L rec-addrs ΞΔ mf)
  (match-define (Meta-function name rules si t/conc t/abs) mf)
  (cond
   [t/abs mf]
   [else
    (define-values (rev-rules* si)
      (for/fold ([rrules '()] [si pure]) ([rule (in-list rules)])
        (define r (abstract-rule L rec-addrs ΞΔ rule))
        (values (cons r rrules) (combine si r))))
    (Meta-function name (reverse rev-rules*) si t/conc #f)]))

;; abstract-rule
(define (abstract-rule L rec-addrs ΞΔ rule)
  (match-define (Rule rule-name lhs rhs binding-side-conditions si) rule)

  ;; Now we rewrite the LHS to non-deterministically choose values when it
  ;; pattern matches on recursive positions.
  ;; FIXME: Space patterns not replaced with their transformed versions.
  (define-values (lhs* lhs-binding-side-conditions lsi)
    (flatten-pattern rec-addrs lhs '() #f))

  ;; Finally we rewrite the binding side-conditions to go between the
  ;; lhs and rhs bindings/side-conditions
  (define-values (binding-side-conditions* bscsi)
    (abstract-bindings rec-addrs ΞΔ (list rule-name) binding-side-conditions
                       (λ (bscs* si)
                          (values (reverse bscs*) (combine lsi si)))))

  ;; We now need to flatten the lhs pattern, and all patterns in binding-side-conditions.
  ;; The RHS pattern needs its recursive positions replaced with allocated addresses and
  ;; corresponding weak updates to the store.

  ;; First we check that no trusted recursive spaces have any variants constructed in rhs.
  (define-values (rhs* store-updates susi)
    (check-and-rewrite-term rec-addrs rule-name rhs))

  (define bscs* (append lhs-binding-side-conditions
                        binding-side-conditions*
                        store-updates))
  (Rule rule-name lhs* rhs* bscs* (combine bscsi susi)))

(define (abstract-bindings rec-addrs ΞΔ rev-addr bscs kont)
  (define bind (bind* rec-addrs ΞΔ))
  (let let-recur ([bindings bscs] [i 0] [bindings* '()] [susi pure])
    (match bindings
      ['() (kont bindings* susi)]
      [(cons binding bindings)
       (define (continue bindings* si)
         (let-recur bindings (add1 i) bindings* (combine si susi)))
       (match binding
         [(Binding pat expr)
          (bind expr
                (cons `(Let-binding ,i) rev-addr)
                (λ (e*)
                   (define-values (pat* bscs-for-pat* si*)
                     (flatten-pattern rec-addrs pat '() #f))
                   (continue (append (reverse (cons (Binding pat* e*) bscs-for-pat*))
                                     bindings*)
                             si*)))]
         [(Store-extend kexpr vexpr trust-strong?)
          (bind kexpr
                (cons `(Let-store-key ,i) rev-addr)
                (λ (k*)
                   (bind vexpr
                         (cons `(Let-store-val ,i) rev-addr)
                         (λ (v*)
                            (continue (cons (Store-extend k* v* trust-strong?) bindings*)
                                      (combine writes k* v*))))))]
         [(When expr)
          (bind expr
                (cons `(When-expr ,i) rev-addr)
                (λ (w*) (continue (cons (When w*) bindings*)
                                  (expression-store-interaction w*))))])])))

;; Encapsulates a pattern in the following function. If recur on expr
;; changes the store, then bind in a let (expresses sequencing), pass the reference to the value.
(define ((bind* rec-addrs ΞΔ) expr path fn [name #f])
  (define e* (abstract-expression* rec-addrs ΞΔ expr path))
  (cond
   [(writes? (expression-store-interaction e*))
    (define var (if name (gensym name) (gensym 'intermediate)))
    (define r (fn (Term pure (Rvar var))))
    (Let (combine e* r)
         (list (Binding (Avar var) e*))
         r)]
   [else (fn e*)]))

;; abstract-expression
;; An EPattern must be abstracted so that Term expressions are rewritten and
;; stores are threaded through meta-function-call's.
;; After this, the binders in the LHS pattern get chosen from the abstract positions like in rules.
;; OPT-OP (ΞΔ): do analysis on meta-functions first to determine if they need to produce new stores,
;;              then only meta-function-call's that produce new stores get marked as changing store.
(define (abstract-expression rec-addrs ΞΔ alloc-tag expr)
  (abstract-expression* rec-addrs ΞΔ expr (list alloc-tag)))

;; FIXME: some output store-interactions are wrong.
(define (abstract-expression* rec-addrs ΞΔ expr rev-addr)
  (define bind (bind* rec-addrs ΞΔ))

  (define (binary e₀ e₁ tag₀ tag₁ container [name₀ #f] [name₁ #f])
    (bind e₀ (cons tag₀ rev-addr)
          (λ (e₀*)
             (bind e₁ (cons tag₁ rev-addr)
                   (λ (e₁*) (container (combine e₀* e₁*) e₀* e₁*))
                   name₁))
          name₀))

  (define (recur expr rev-addr)
    (match expr
     [(Term _ pattern)
      ;; We use the path taken to this expr as the tag for allocation.
      (define-values (pat* store-updates si)
        (check-and-rewrite-term rec-addrs (reverse rev-addr) pattern))
      ;; If no store updates, then no new store.
      (cond
       [(empty? store-updates) (Term pure pat*)]
       [else (Let si store-updates (Term pure pat*))])]

     [(Store-lookup _ kexpr)
      (bind kexpr
            (cons 'SL-key rev-addr)
            (λ (k*)
               (define slsi (combine reads k*))
               (Choose (add-many slsi) (gensym) (Store-lookup slsi k*)))
            'key)]
;; FIXME arg* not necessarily a pattern
     [(Meta-function-call _ name arg-pat)
      (bind (Term pure arg-pat)
            (cons 'MF-arg rev-addr)
            (λ (arg*)
               (define si (hash-ref ΞΔ name read/write/alloc/many))
               (Meta-function-call si name arg*)))]

     [(If _ g t e)
      (bind g
            (cons 'If-guard rev-addr)
            (λ (g*)
               (define t* (recur t (cons 'If-then rev-addr)))
               (define e* (recur e (cons 'If-else rev-addr)))
               (If (combine g* t* e*) g* t* e*)))]

     [(Equal _ lexpr rexpr)
      (binary lexpr rexpr 'Equal-left 'Equal-right
              (λ (si l* r*) (Equal (add-many si) l* r*)))]

     ;; Let is tricky since it might have rebindings of the store, which need to be forwarded as the
     ;; next store when translation goes forward.

     [(Let _ bindings body)
      ;; In order to not get generated lets in let clauses,
      ;; we bind Binding RHSs to variables that then get matched against their pattern.
      (abstract-bindings
       rec-addrs
       ΞΔ
       rev-addr
       bindings
       (λ (bindings* susi)
          (cond
           [(empty? bindings*) (recur body rev-addr)]
           [else
            (bind body
                  (cons 'Let-body rev-addr)
                  (λ (b*)
                     (Let (combine susi b*)
                          (reverse bindings*)
                          b*)))])))]

     [(Choose _ ℓ cexpr)
      (bind cexpr
            (cons 'Choose-expr rev-addr)
            (λ (ec*) (Choose (combine many ec*) ℓ ec*)))]

;;; Map operations
     
     [(Map-lookup _ m kexpr default? dexpr)
      (bind kexpr
            (cons 'ML-key rev-addr)
            (λ (k*)
               (cond
                [default?
                  (bind dexpr
                        (cons 'ML-default rev-addr)
                        (λ (d*)
                           (Map-lookup (combine k* d*) m k* #t d*))
                        'default)]
                [else (Map-lookup (combine k*) m k* #f #f)]))
            'key)]

     [(Map-extend _ m kexpr vexpr trust-strong?)
      (binary kexpr vexpr 'ME-key 'ME-val
              (λ (si k* v*) (Map-extend si m k* v* trust-strong?)) 'key)]

     [(Map-remove _ mvar kexpr)
      (bind kexpr
            (cons 'Map-remove-key rev-addr)
            (λ (k*) (Map-remove (combine many k*) mvar k*)))]

     [(In-Dom? _ mvar kexpr)
      (bind kexpr
            (cons 'In-Dom?-key rev-addr)
            (λ (k*) (In-Dom? (combine many k*) mvar k*)))]

     [(Empty-map _ container)
      (if (procedure? container)
          expr
          (bind container (cons 'Empty-map-abstraction rev-addr)
                (λ (c*) (Empty-map (combine c*) c*))))]

     ;; Map-empty? at end

;;; Set operations

     [(or (Set-Add* _ sexpr vexprs)
          (Set-Remove* _ sexpr vexprs)
          (Set-Intersect _ sexpr vexprs)
          (Set-Union _ sexpr vexprs)
          (Set-Subtract _ sexpr vexprs))
      (define-values (base container)
        (cond [(Set-Add*? expr) (values 'Set-Add* Set-Add*)]
              [(Set-Union? expr) (values 'Set-Union Set-Union)]
              [(Set-Remove*? expr) (values 'Set-Remove* Set-Remove*)]
              [(Set-Intersect? expr) (values 'Set-Intersect Set-Intersect)]
              [(Set-Subtract? expr) (values 'Set-Subtract Set-Subtract)]))
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
                       ['() (container si s* (reverse vexprs*))]
                       [(cons v vexprs)
                        (bind v
                              (cons (list arg-tag i) rev-addr)
                              (λ (v*)
                                 (set-op-recur vexprs (add1 i) (cons v* vexprs*)
                                               (combine si v*))))])))))]

     [(In-Set? _ sexpr vexpr)
      (binary sexpr vexpr 'In-Set?-set 'In-Set?-value
              (λ (si s* v*) (In-Set? (add-many si) s* v*)))]

     [(Set-empty? _ sexpr)
      (bind sexpr
            (cons 'Set-empty-val rev-addr)
            (λ (s*) (Set-empty? (combine many s*) s*)))]

     [(Empty-set _ container)
      (if (procedure? container)
          expr
          (bind container (cons 'Empty-set-abstraction rev-addr)
                (λ (c*) (Empty-set (combine c*) c*))))]

;; Add qualification to allocation position
     [(SAlloc si space)
      (QSAlloc allocs space (reverse rev-addr))]
     [(MAlloc si space)
      (QMAlloc allocs space (reverse rev-addr))]

     [(or (? Boolean?) (? Unsafe-store-ref?) (? Unsafe-store-space-ref?)
          (? QSAlloc?) (? QSAlloc?) (? Map-empty??))
      expr]
     [_ (error 'abstract-expression "Bad expression ~a" expr)]))
  (recur expr rev-addr))

