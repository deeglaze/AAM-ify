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

ADDITIONAL FEATURES:
- abstract counting for better equality matching

WISHLIST (! is done):
+ build an escape hatch for smarter lattices.
! make "address spaces" that divvy items amongst as many stores that get automatically added.
  currently there is one address space --- the required store component in each rewrite rule.
! Extend address spaces to be mutable or immutable.
+ widening for control flow
+ automatic garbage collection in (to add) "weak maps" across address spaces.
  Addresses of different spaces can occur in mapped objects.
+ pattern support for sets and maps (currently we use side-conditions)

FIXMEs:
- Recursive positions replaced with (Address-Space) are expected to be structurally compared for equality,
  but spaces that already use (Address-Space) are expected to addresses themselves.
  This nuance is lost in translation.
- We need to track positions where maps flow, and what the expected spaces are, so we can mark them
  as abstract (with pointer to cardinality analysis) or not when constructing them.
- Synthesize a skeleton alloc function.
|#

(require graph
         racket/unsafe/ops
         racket/trace
         "spaces.rkt"
         "shared.rkt")
(provide abstract-language abstract-rule
         alloc-skeleton)

;; language->graph : Language → unweighted-directed-graph
(define (language-spaces->graph spaces)
  (define LG (unweighted-graph/directed '()))
  (define Space-nodes (add-space-nodes! LG spaces))
  (for ([(name space) (in-dict spaces)])
    (add-space-edges! LG Space-nodes name space))
  LG)

;; An Endpoint is an (Endpoint Variant-Address Space-Name)
(struct Endpoint (address space) #:transparent)
(struct Space-node (name trust) #:transparent)
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
                [(User-Space variants trust-recursion?)
                 (define node (Space-node name trust-recursion?))
                 (define self-node (Space-ref-node node))
                 (unless (has-vertex? G node)
                   (add-vertex! G node)
                   (add-vertex! G self-node)
                   (add-directed-edge! G self-node node))
                 node]))))

(define (add-space-edges! G Space-nodes name space)
  (match space
    [(User-Space variants-or-components trust-recursion?)
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
(define (language-recursive-spaces spaces)
  (define LG (language-spaces->graph spaces))
  ;; Do a little error checking while discovering recursion.
  (define recursive-islands (scc LG))
  ;; Make a map of Space-name to Set[spaces recursive with Space]
  (for/fold ([h ρ₀]) ([cc (in-list recursive-islands)]
                      #:unless (match cc
                                 ;; The reference nodes themselves are administrative.
                                 [(list (? Space-ref-node?)) #t] [_ #f]))
      (define spaces
        (for/set ([c (in-list cc)] #:when (Space-ref-node? c)) (Space-ref-node-sn c)))
      (define space-names
        (for/set ([space (in-set spaces)]) (Space-node-name space)))
      (define-values (h* dummy)
       (for/fold ([h h] [trust 'unspecified]) ([space (in-set spaces)])
         (define ctrust (Space-node-trust space))
         (cond [(or (eq? trust 'unspecified) (equal? trust ctrust))
                (values (hash-set h (Space-node-name space) space-names) ctrust)]
               [else
                (error 'bad-trust "Recursive spaces have mismatched recursion trust ~a" cc)])))
      h*))

(define (language-abstract-spaces-and-recursive-positions spaces recursive-spaces)
  ;; Seed the abstract space map with defaults we know.
  (define abstract-spaces₀
    (for/fold ([h ρ₀]) ([(name space) (in-dict spaces)])
      (match space
        [(External-Space _ _ imprecise? _)
         (hash-set h name imprecise?)]
        [(Address-Space space)
         (hash-set h name #t)]
        [(User-Space _ trust-recursion?)
         (hash-set h name (if trust-recursion? #f ∅))])))

  ;; Find all recursive addresses and build the first pass of abstract-spaces.
  (define-values (variant-rec-addrs abstract-spaces₁)
    (for/fold ([rec-addrs ρ₀] [abstract-spaces abstract-spaces₀])
        ([(name space) (in-dict spaces)])
      (match space
        [(or (? External-Space?) (? Address-Space?)) (values rec-addrs abstract-spaces)]
        [(User-Space variants-or-components trusted?)
         (cond
          [trusted?
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
;; FIXME: maps with abstract domains need to be specially marked for careful treatment by the semantics.
;;        As such, we can make the following concessions:
;;        If a space has any abstract map components, there can only be one map component.
;;        Otherwise, abstract maps need Variant tagging (XXX: can we do this automatically?) to
;;        ensure that we identify the maps in the semantics that need cardinality analysis.
(define (abstract-language L)
  ;; We first turn L into a graph in the following way:
  ;; External spaces and (Address-Space) are terminal nodes (no outgoing edges).
  ;; Space names are nodes that point to all of their variant nodes' Variant-Addresses
  ;; (Space-reference name) is treated as the node for name.

  ;; All space names (S) that are in the same strongly connected component are treated as
  ;; recursive. That is, for the Variants-or-Components in S, any (Space-reference name) is
  ;; replaced by (Address-Space) when name ∈ S, and the address of the position is added to
  ;; the recursive mention map.

  (match-define (Language lang-name spaces) L)
  (define recursive-spaces (language-recursive-spaces spaces))
  (define-values (abstract-spaces variant-rec-addrs)
    (language-abstract-spaces-and-recursive-positions spaces recursive-spaces))

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
             (values comp (hash-ref abstract-spaces name (λ () (error 'replace-component "Impossible")))))]
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

    (match variant-or-component
      [(Variant name comps)
       (define abs-comps
         (for/vector #:length (vector-length comps)
                     ([comp (in-vector comps)])
           (define-values (abs-comp dummy)
             (replace-recursive-mentions-in-component comp))
           abs-comp))
       (Variant name abs-comps)]
      [comp
       (define-values (abs-comp dummy)
         (replace-recursive-mentions-in-component comp))
       abs-comp]))

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

           [(User-Space variants trust-recursion?)
            (define abs-variants
              (for/list ([variant (in-list variants)])
                (replace-recursive-mentions name variant)))

            ;; If recursion is trusted, don't give rewritten form.
            ;; We just did that to get the recursive addresses.
            ;; FIXME: is doing this necessary at all if trust-recursion?
            (if trust-recursion?
                space
                (User-Space abs-variants trust-recursion?))]))

       (hash-set abs-spaces name abs-space)))

   (values (Language lang-name abs-spaces)
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
              [else
               ;; If name is abstract, then so is current-space.
               (hash-join abs-spaces current-space (set-add dependents name))])]))])]
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
    [(Variant name comps)
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
     ;; XXX: What do we do with recursive mentions in components that aren't
     ;; under a Variant?
     (values rec-addrs abs-spaces*)]))

;; Resolve any left-over dependencies for abstraction.
;; When backchaining, fill out table with intermediate results.
(define (search-space-abstract abs-spaces space-name)
  (define catch-self (mutable-set))
  (define-values (abs-spaces* dummy)
    (let loop ([abs-spaces abs-spaces] [space-name* space-name])
      (when (set-member? catch-self space-name*)
        (error 'search-space-abstract "Uncaught recursion on ~a given ~a" space-name abs-spaces))
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
    [(Variant name comps)
     (define len (vector-length comps))
     (let build ([i 0])
       (if (= i len)
           ∅
           (set-union (build (add1 i))
                      (for/set ([endpoint (in-set (component->endpoints (unsafe-vector-ref comps i)))])
                        (match-define (Endpoint addr space) endpoint)
                        (Endpoint (cons (Variant-field name i) addr) space)))))]
    [comp (for/set ([endpoint (in-set (component->endpoints comp))])
            (match-define (Endpoint addr space) endpoint)
            (Endpoint (cons (Space-component name) addr) space))]))

;; Any deep pattern that recurs through an address gets turned into a non-deterministic match.
;; That is, if we have a pattern (say Pat) in a recursive position,
;;  - we create a fresh Bvar (say B) and
;;  - add a binding to the rule (Binding Pat (Choose (Store-lookup (Term (Rvar B)))))
;;  - Repeat the process for Pat.
(define (emit-binding-sc rec-addrs pat)
  (define new-bvar (gensym))
  (if (variant? pat)
      (let-values ([(pat* binding-scs) (flatten-pattern rec-addrs pat '() #f)])
        (values (Bvar new-bvar (Address-Space 'AAM))
                (cons (Binding pat* (Choose #t (Store-lookup #t (Term #t (Rvar new-bvar)))))
                      binding-scs)))
      (values (Bvar new-bvar (Address-Space 'AAM))
              (list (Binding pat (Choose #t (Store-lookup #t (Term #t (Rvar new-bvar)))))))))

;; flatten-pattern : Pattern Option[Set[List[Component-Address]]] → (values Pattern List[Binding-side-conditions])
(define (flatten-pattern rec-addrs pat rev-addr [rec-positions #f])
  (cond [(and rec-positions (set-member? rec-positions (reverse rev-addr)))
         (emit-binding-sc rec-addrs pat)]
        [else
         (match pat
           [(variant (and v (Variant name _)) pats)
            ;; Trusted spaces' variants are all given an empty set of recursive references.
            (define rec-positions (hash-ref rec-addrs name ∅))
            (define pats* (make-vector (vector-length pats)))
            ;; OPT-OP: consider an RRB-tree for binding-scs if it's a bottleneck.
            (define binding-scs*
              (for/fold ([binding-scs '()])
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
                (define-values (pat* binding-scs*)
                  (flatten-pattern rec-addrs pat (list (Variant-field name i)) indexed-addresses))
                (unsafe-vector-set! pats* i pat*)
                (append (reverse binding-scs*) binding-scs)))
            (values (variant v pats*)
                    (reverse binding-scs*))]
           [(Rvar x) (error 'flatten-pattern "Unexpected reference in match pattern ~a" x)]
           [other (values other '())])]))

(define (check-and-rewrite-term rec-addrs alloc-tag tm)
  ;; if current position is recursive, hoist pattern out into allocation+store-update.
  ;; Hoist inside-out in order to do it in one pass.
  (define (recur current-variant rev-addr rev-local-addr tm)
    (define rec-addresses
      (if current-variant (hash-ref rec-addrs current-variant ∅) ∅))
    (cond
     [(set-member? rec-addresses (reverse rev-local-addr))
      (define address-var (gensym))
      (define-values (pat* store-updates)
        (recur #f rev-addr '() tm))
      (define store** (gensym 'σ))
      (values (Rvar address-var)
              (append store-updates
                      (list (Binding (Avar address-var)
                                     (QSAlloc #f 'AAM (cons alloc-tag (reverse rev-addr))))
                            (Store-extend (Term #t (Rvar address-var))
                                          (Term #t pat*)
                                          #f))))]
     [else
      (match tm
        [(Bvar x _) (error 'abstract-rule "Rule RHS may not bind ~a" tm)]
        [(variant (and v (Variant name _)) pats)
         (define len (vector-length pats))
         (define pats* (make-vector len))
         ;; TODO?: error/warn if space defining vname is trusted.
         ;;        Or have second tag trusting construction
         (define store-updates
           (let rewrite-pats ([i 0]
                              [rev-store-updates '()])
             (cond
              [(= i len) (reverse rev-store-updates)]
              [else
               (define pat (unsafe-vector-ref pats i))
               (define vfield (Variant-field name i))
               (define-values (pat* store-updates*)
                 (recur name (cons vfield rev-addr)
                        (list vfield)
                        pat))
               (unsafe-vector-set! pats* i pat*)
               (rewrite-pats (add1 i)
                             (append (reverse store-updates*) rev-store-updates))])))
         (values (variant v pats*) store-updates)]
        [other (values other '())])]))
  (recur #f '() '() tm))

(define (abstract-meta-function L rec-addrs ΞΔ mf)
  (match-define (Meta-function name rules trusted-implementation/conc trusted-implementation/abs) mf)
  (cond
   [trusted-implementation/abs mf]
   [else
    (define rules* (for/list ([rule (in-list rules)]) (abstract-rule L rec-addrs ΞΔ rule)))
    (Meta-function name rules* trusted-implementation/conc #f)]))

;; abstract-rule
;; store-name is the Bvar that denotes "the store" in every LHS pattern. There must be one.
(define (abstract-rule L rec-addrs ΞΔ rule)
  (match-define (Rule rule-name lhs rhs binding-side-conditions) rule)

  ;; Now we rewrite the LHS to non-deterministically choose values when it
  ;; pattern matches on recursive positions.
  (define-values (lhs* lhs-binding-side-conditions)
    (flatten-pattern rec-addrs lhs '() #f))

  ;; Finally we rewrite the binding side-conditions to go between the
  ;; lhs and rhs bindings/side-conditions
  (define binding-side-conditions*
    (abstract-bindings rec-addrs ΞΔ (list rule-name) binding-side-conditions reverse))

  ;; We now need to flatten the lhs pattern, and all patterns in binding-side-conditions.
  ;; The RHS pattern needs its recursive positions replaced with allocated addresses and
  ;; corresponding weak updates to the store.

  ;; First we check that no trusted recursive spaces have any variants constructed in rhs.
  (define-values (rhs* store-updates)
    (check-and-rewrite-term rec-addrs rule-name rhs))

  (Rule rule-name lhs* rhs* (append lhs-binding-side-conditions
                                    binding-side-conditions*
                                    store-updates)))

(define (abstract-bindings rec-addrs ΞΔ rev-addr bscs kont)
  (define bind (bind* rec-addrs ΞΔ))
  (let let-recur ([bindings bscs] [i 0] [bindings* '()])
    (match bindings
      ['() (kont bindings*)]
      [(cons binding bindings)
       (define (continue bindings*) (let-recur bindings (add1 i) bindings*))
       (match binding
         [(Binding pat expr)
          (bind expr
                (cons `(Let-binding ,i) rev-addr)
                (λ (e*)
                   (define-values (pat* bscs-for-pat*)
                     (flatten-pattern rec-addrs pat '() #f))
                   (continue (append (reverse (cons (Binding pat* e*) bscs-for-pat*))
                                     bindings*))))]
         [(Store-extend kexpr vexpr trust-strong?)
          (bind kexpr
                (cons `(Let-store-key ,i) rev-addr)
                (λ (k*)
                   (bind vexpr
                         (cons `(Let-store-val ,i) rev-addr)
                         (λ (v*)
                            (continue (cons (Store-extend k* v* trust-strong?) bindings*))))))]
         [(When expr)
          (bind expr
                (cons `(When-expr ,i) rev-addr)
                (λ (w*) (continue (cons (When w*) bindings*))))])])))
  
;; Encapsulates a pattern in the following function. If recur on expr
;; changes the store, then bind in a let (expresses sequencing), pass the reference to the value.
(define ((bind* rec-addrs ΞΔ) expr path fn [name #f])
  (define-values (e* Δ?) (abstract-expression* rec-addrs ΞΔ expr path))
  (cond
   [Δ?
    (define var (if name (gensym name) (gensym 'intermediate)))
    (define-values (r dummy) (fn (Term #t (Rvar var))))
    (values (Let (list (Binding (Avar var) e*)) r) #t)]
   [else (fn e*)]))

;; abstract-expression
;; An EPattern must be abstracted so that Term expressions are rewritten and
;; stores are threaded through meta-function-call's.
;; After this, the binders in the LHS pattern get chosen from the abstract positions like in rules.
;; OPT-OP (ΞΔ): do analysis on meta-functions first to determine if they need to produce new stores,
;;              then only meta-function-call's that produce new stores get marked as changing store.
(define (abstract-expression rec-addrs ΞΔ alloc-tag expr)
  (abstract-expression* rec-addrs ΞΔ expr (list alloc-tag)))

(define (abstract-expression* rec-addrs ΞΔ expr rev-addr)
  (define bind (bind* rec-addrs ΞΔ))
  (let recur ([expr expr] [rev-addr rev-addr])
   (match expr
     [(Term si pattern)
      ;; We use the path taken to this expr as the tag for allocation.
      (define-values (pat* store-updates)
        (check-and-rewrite-term rec-addrs (reverse rev-addr) pattern))
      ;; If no store updates, then no new store.
      (cond
       [(empty? store-updates) (values (Term #t pat*) #f)]
       [else (values (Let #f store-updates (Term #t pat*)) #t)])]

     [(Store-lookup si kexpr)
      (bind kexpr
            (cons 'SL-key rev-addr)
            (λ (k*)
               (values (Choose si (Store-lookup si k*)) #f))
            'key)]

     ;; TODO: mark maps as abstract or not for correct abstraction.
     [(Map-lookup si m kexpr default? dexpr)
      (bind kexpr
            (cons 'ML-key rev-addr)
            (λ (k*)
               (cond
                [default?
                  (bind dexpr
                        (cons 'ML-default rev-addr)
                        (λ (d*)
                           (values (Map-lookup si m k* #t d*) #f))
                        'default)]
                [else (values (Map-lookup si m k* #f #f) #f)]))
            'key)]

     [(Map-extend si m kexpr vexpr trust-strong?)
      (bind kexpr
            (cons 'ME-key rev-addr)
            (λ (k*)
               (bind vexpr
                     (cons 'ME-val rev-addr)
                     (λ (v*)
                        (values (Map-extend si m k* v* trust-strong?) #f))))
            'key)]

     [(Meta-function-call si name arg-pat)
      (bind (Term #t arg-pat)
            (cons 'MF-arg rev-addr)
            (λ (arg*)
               (values (Meta-function-call si name arg*)
                       ;; Consider store changes if Meta-function can change store.
                       ;; Conservatively assume they can change.
                       (hash-ref ΞΔ name #t))))]

     [(If si g t e)
      (bind g
            (cons 'If-guard rev-addr)
            (λ (g*)
               (define-values (t* tΔ?) (recur t (cons 'If-then rev-addr)))
               (define-values (e* eΔ?) (recur e (cons 'If-else rev-addr)))
               (values (If si g* t* e*) (or tΔ? eΔ?))))]

     ;; Let is tricky since it might have rebindings of the store, which need to be forwarded as the
     ;; next store when translation goes forward.

     [(Let si bindings body)
      ;; In order to not get generated lets in let clauses,
      ;; we bind Binding RHSs to variables that then get matched against their pattern.
      (abstract-bindings
       rec-addrs
       ΞΔ
       rev-addr
       bindings
       (λ (bindings*)
          (cond
           [(empty? bindings*) (recur body rev-addr)]
           [else
            (bind body
                  (cons 'Let-body rev-addr)
                  (λ (b*) (values (Let si (reverse bindings*) b*) #f)))])))]

     [(Equal si lexpr rexpr)
      (bind lexpr
            (cons 'Equal-left rev-addr)
            (λ (l*)
               (bind rexpr
                     (cons 'Equal-right rev-addr)
                     (λ (r*)
                        (values (Equal si l* r*) #f)))))]

     [(In-Dom si mvar kexpr)
      (bind kexpr
            (cons 'In-Dom-key rev-addr)
            (λ (k*) (values (In-Dom si mvar k*) #f)))]

     [(Set-Union si sexprs)
      (if (empty? sexprs)
          (values (Empty-set) #f)
          (let union-recur ([sexprs sexprs] [i 0] [sexprs* '()])
            (match sexprs
              ['() (values (Set-Union si (reverse sexprs*)) #f)]
              [(cons s sexprs)
               (bind s
                     (cons `(Set-Union ,i) rev-addr)
                     (λ (s*)
                        (union-recur sexprs (add1 i) (cons s* sexprs*))))])))]

     [(Set-Add* si sexpr vexprs)
      (if (empty? vexprs)
          (recur sexpr rev-addr)
          (bind sexpr
                (cons 'Set-Add*-set rev-addr)
                (λ (s*)
                   (let add*-recur ([vexprs vexprs] [i 0] [vexprs* '()])
                     (match vexprs
                       ['() (values (Set-Add* si s* (reverse vexprs*)) #f)]
                       [(cons v vexprs)
                        (bind v
                              (cons `(Set-Add*-val ,i) rev-addr)
                              (λ (v*)
                                 (add*-recur vexprs (add1 i) (cons v* vexprs*))))])))))]
      
     [(In-Set si sexpr vexpr)
      (bind sexpr
            (cons 'In-Set-set rev-addr)
            (λ (s*)
               (bind vexpr 
                     (cons 'In-Set-value rev-addr)
                     (λ (v*)
                        (values (In-Set si s* v*) #f)))))]

     [(SAlloc si space)
      (values (QSAlloc si space (reverse rev-addr)) #f)]
     [(MAlloc si space)
      (values (QMAlloc si space (reverse rev-addr)) #f)]

     [(or (? boolean?) (? Empty-set?) (? Unsafe-store-ref?)
          (? QSAlloc?) (? QSAlloc?))
      (values expr #f)]
     [_ (error 'abstract-expression "Bad expression ~a" expr)])))

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
               (match-define (Rule name lhs rhs bscs) rule)
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
    [(or (Choose _ expr)
         (Store-lookup _ expr)
         (In-Dom _ _ expr))
     (expression-hints expr tail)]
    [(or (? SAlloc?) (? MAlloc?))
     (error 'expression-hints "Unqualified allocation ~a" expr)]
    [(or (QSAlloc _ _ hint) (QMAlloc _ _ hint)) (cons hint tail)]
    [(or (Equal _ expr0 expr1)
         (Map-lookup _ _ expr0 _ expr1)
         (Map-extend _ _ expr0 expr1 _)
         (In-Set _ expr0 expr1))
     (expression-hints expr0 (if expr1 (expression-hints expr1 tail) tail))]
    [(If _ g t e)
     (expression-hints g (expression-hints t (expression-hints e tail)))]
    [(Let _ bscs bexpr)
     (bscs-hints bscs (expression-hints bexpr tail))]
    [(Set-Union _ exprs) (hint-map expression-hints exprs tail)]
    [(Set-Add* _ expr exprs)
     (expression-hints expr (hint-map expression-hints exprs tail))]
    [_ tail]))

;; [1] Might and Shivers ICFP 2006 "Improving flow analyses via ΓCFA: Abstract garbage collection and counting"
