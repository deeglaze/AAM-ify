#lang racket

#|
This module is a proof of concept that the allocation function and abstract abstract machine
for a semantics in a restricted language can be partially automatically generated from
the declarations of state spaces and reduction rules.

The key ideas:
* use graphs algorithms to find recursive mentions of a space to change out with Addr
* reduction relation can strongly update non-store functions (they will be made finite)
* all store updates are made weak
* all store lookups are made non-deterministic
* Recursive data structure construction sites are counted to inform alloc how many addresses to create.
* ASSUMPTION: distinct addresses are desired for these syntactically distinct allocation points.
*
|#

(require graph
         racket/trace
         "AAM-spaces.rkt"
         "AAM-shared.rkt")
(provide abstract-language abstract-rule)

;; Abstract counting algebra
(define/match (⊕ c₀ c₁)
  [(0 c) c]
  [(c 0) c]
  [(_ _) 'ω])

(define/match (cmax c₀ c₁)
  [(0 c) c]
  [(c 0) c]
  [(1 c) c]
  [(c 1) c]
  [(_ _) 'ω])

(define/match (c⊑ c₀ c₁)
  [(c c) #t]
  [(0 c) #t]
  [(1 'ω) #t]
  [(_ _) #f])

(define (μ+ μ a c) (hash-set μ (⊕ c (hash-ref μ a 0))))
(define (μmax μ a c) (hash-set μ (cmax c (hash-ref μ a 0))))
(define (μ⊔ μ₀ μ₁) (for/fold ([μ μ₀]) ([(a c) (in-dict μ₁)]) (μmax μ a c)))

;; language->graph : Language → unweighted-directed-graph
(define (language-spaces->graph spaces)
  (define LG (unweighted-graph/directed '()))
  (define Space-nodes (add-space-nodes! LG spaces))
  (for ([(name space) (in-dict spaces)])
    (add-space-edges! LG Space-nodes name space))
  LG)

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
                 (unless (has-vertex? G node) (add-vertex! G node))
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
             (hash-ref Space-nodes space
                       (λ () (error 'add-space-edges!
                                    "Space ~a refers to unknown space ~a" name space)))))
       (add-directed-edge! G node addr)
       (add-directed-edge! G addr space-node))]
    [_ (void)]))

;; abstract-language : Language → (values Language Map[Variant-name,Set[Variant-Address]] Map[Space-name,Boolean])
;; Returns a language that cuts all recursion out into addresses,
;; a map from variants to positions of self-reference (and mutually-recursive references),
;; and a map from space names to whether or not they are "abstract."
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
  (define LG (language-spaces->graph spaces))

  ;; Do a little error checking while discovering recursion.
  (define recursive-islands (scc LG))
  ;; Make a map of Space-name to Set[spaces recursive with Space]
  (define recursive-spaces
    (for/fold ([h ρ₀]) ([cc (in-list recursive-islands)])
      (define spaces (list->set (filter Space-node? cc)))
      (define space-names (for/set ([space (in-set spaces)]) (Space-node-name space)))
      (define-values (h* dummy)
       (for/fold ([h h] [trust 'unspecified]) ([space (in-set spaces)])
         (define ctrust (Space-node-trust space))
         (cond [(or (eq? trust 'unspecified) (equal? trust ctrust))
                (values (hash-set h (Space-node-name space) space-names) ctrust)]
               [else
                (error 'bad-trust "Recursive spaces have mismatched recursion trust ~a" cc)])))
      h*))

  ;; Seed the abstract space map with defaults we know.
  (define abstract-spaces₀
    (for/fold ([h ρ₀]) ([(name space) (in-dict spaces)])
      (match space
        [(External-Space _ _ imprecise?)
         (hash-set h name imprecise?)]
        [(Address-Space)
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
             (values (Address-Space) #t)
             ;; Non-recursive references are not replaced, even if the spaces are abstract.
             (values comp (hash-ref abstract-spaces name (λ () (error 'replace-component "Impossible")))))]
        [(℘ comp) (replace-recursive-mentions-in-component comp)]
        [(Map domain range)
         (define-values (abs-dom dom-abs?)
           (replace-recursive-mentions-in-component domain))
         (define-values (abs-range rng-abs?)
           (replace-recursive-mentions-in-component range))
         ;; If a map domain contains addresses, the map is now treated as
         ;; m(a) = b implies ∃ A ∈ γ(a). A ↦ b, but we don't know if A is actually in the map.
         ;; Additionally, the Map now becomes weak, so b is lifted implicitly to a powerset domain.
         ;; TODO: build an escape hatch for smarter lattices.
         (cond [dom-abs? (values (Map abs-dom (℘ abs-range)) #t)]
               [else (values (Map abs-dom abs-range) rng-abs?)])]
        [(Address-Space) (values comp #t)]))
    (trace replace-recursive-mentions-in-component)

    (match variant-or-component
      [(Variant name comps)
       (define abs-comps
         (for/list ([comp (in-list comps)]
                    [i (in-naturals)])
           (define-values (abs-comp dummy)
             (replace-recursive-mentions-in-component comp))
           abs-comp))
       (Variant name abs-comps)]
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
            spaces]

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

   (values (Language lang-name abs-spaces) variant-rec-addrs abstract-spaces))

;; find-recursive-mentions :
;;  Space-name (∪ Variant Component) Map[Variant-name,Variant-Address] Rec-Space-Map →
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
            [#t (hash-set-if-unresolved abs-spaces current-space #t)] ;; known recursive (already set if trusted)
            [#f abs-spaces] ;; known non-recursive
            ;; unknown. Add to set of names to resolve after finishing.
            [dependents
             (when (boolean? (hash-ref abs-spaces current-space -unmapped))
               (error 'find-recursive-mentions-in-component
                      "Impossible state? Expect co-trust to be checked before getting here."))
             (hash-join abs-spaces current-space (set-add dependents name))]))])]
      [(℘ comp)
       (find-recursive-mentions-in-component comp (cons '℘ rev-addr) abs-spaces)]
      [(Map domain range)
       (define-values (rec-addresses abs-spaces*)
         (find-recursive-mentions-in-component domain (cons 'domain rev-addr) abs-spaces))
       (define-values (rec-addresses* abs-spaces**)
         (find-recursive-mentions-in-component range (cons 'range rev-addr) abs-spaces*))
       (values (set-union rec-addresses rec-addresses*) abs-spaces**)]
      [(Address-Space) (values ∅ (hash-set abs-spaces current-space #t))]))

  (match variant-or-component
    [(Variant name comps)
     (for/fold ([rec-addrs* rec-addrs] [abs-spaces* abs-spaces])
         ([comp (in-list comps)]
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
      (when (set-member? catch-self space-name)
        (error 'space-abstract? "Uncaught recursion on ~a given ~a" space-name abs-spaces))
      (set-add! catch-self space-name*)
      (match (hash-ref abs-spaces space-name)
        [(? boolean? b) (values abs-spaces b)]
        [deps (hash-set abs-spaces
                        space-name*
                        (for/fold ([h abs-spaces] [b #f])
                            ([dep (in-set deps)])
                          (define-values (h* b*) (loop h dep))
                          (values h* (or b* b))))])))
  abs-spaces*)

(define (component->endpoints comp)
  (let build ([comp comp] [rev-addr '()])
    (match comp
      [(Space-reference name) (set (Endpoint (reverse rev-addr) name))]
      [(℘ comp) (build comp (cons '℘ rev-addr))]
      [(Map domain range)
       (set-union (build domain (cons 'domain rev-addr))
                  (build range (cons 'range rev-addr)))]
      [(Address-Space) (set (Endpoint (reverse rev-addr) comp))]
      [_ (error 'component->endpoints "Bad component ~a" comp)])))

;; variant->endpoints : Variant → Set[Endpoint]
;; compute all Variant-Addresses to a terminal space name for a given variant.
(define (variant-or-component->endpoints name v)
  (match v
    [(Variant name comps)
     (let build ([i 0] [comps comps])
       (match comps
         ['() ∅]
         [(cons comp comps)
          (set-union (build (add1 i) comps)
                     (for/set ([endpoint (in-set (component->endpoints comp))])
                       (match-define (Endpoint addr space) endpoint)
                       (Endpoint (cons (Variant-field name i) addr) space)))]))]
    [comp (for/set ([endpoint (in-set (component->endpoints comp))])
            (match-define (Endpoint addr space) endpoint)
            (Endpoint (cons (Space-component name) addr) space))]))

(define (rule-lookup rules name)
  (for/or ([rule (in-list rules)] #:when (equal? name (Rule-name rule))) rule))

;; abstract-rule
;; store-name is the Bvar that denotes "the store" in every LHS pattern. There must be one.
(define (abstract-rule L rec-addrs store rule)
  (match-define (Rule rule-name lhs rhs binding-side-conditions) rule)
  ;; Any deep pattern that recurs through an address gets turned into a non-deterministic match.
  ;; That is, if we have a pattern (say Pat) in a recursive position,
  ;;  - we create a fresh Bvar (say B) and
  ;;  - add a binding to the rule (EBinding Pat (Choose (Map-lookup store-name B no-default)))
  ;;  - Repeat the process for Pat.

  (define (emit-binding-sc pat)
    (define new-bvar (gensym))
    (if (Variant? pat)
        (let-values ([(pat* binding-scs) (flatten-pattern pat '() #f)])
          (values (Bvar new-bvar (Address-Space))
                  (cons (EBinding pat* (Choose (Map-lookup store (Rvar new-bvar) #f #f)))
                        binding-scs)))
        (values (Bvar new-bvar (Address-Space))
                (list (EBinding pat (Choose (Map-lookup store (Rvar new-bvar) #f #f)))))))

  ;; flatten-pattern : Pattern Option[Set[List[Component-Address]]] → (values Pattern List[Binding-side-conditions])
  (define (flatten-pattern pat rev-addr [rec-positions #f])
    (cond [(and rec-positions (set-member? rec-positions (reverse rev-addr)))
           (emit-binding-sc pat)]
          [else
           (match pat
             [(Variant name pats)
              ;; Trusted spaces' variants are all given an empty set of recursive references.
              (define rec-positions (hash-ref rec-addrs name ∅))
              (define-values (pats* binding-scs*)
                (for/fold ([acc '()] [binding-scs '()])
                    ([pat (in-list pats)]
                     [i (in-naturals)])
                  (define indexed-addresses
                    (for/set ([pos (in-set rec-positions)]
                              #:when (match pos
                                       [(cons (Variant-field (== name eq?)
                                                             (== i equal?))
                                              rest) #t]
                                       [_ #f]))
                      pos))
                  (define-values (pat* binding-scs*)
                    (flatten-pattern pat (list (Variant-field name i)) indexed-addresses))
                  (values (cons pat* acc) (append (reverse binding-scs*) binding-scs))))
              (values (Variant name (reverse pats*))
                      (reverse binding-scs*))]
             [(Rvar x) (error 'flatten-pattern "Unexpected reference in match pattern ~a" x)]
             [other (values other '())])]))
  (trace flatten-pattern emit-binding-sc)

  ;; We now need to flatten the lhs pattern, and all patterns in binding-side-conditions.
  ;; The RHS pattern needs its recursive positions replaced with allocated addresses and
  ;; corresponding weak updates to the store.

  ;; First we check that no trusted recursive spaces have any variants constructed in rhs.
  (define-values (rhs* store-updates store*)
   (let check-and-rewrite-rhs ([rhs rhs]
                               [current-variant #f]
                               [store store]
                               [rev-addr '()]
                               [rev-local-addr '()])
     ;; if current position is recursive, hoist pattern out into allocation+store-update.
     ;; Hoist inside-out in order to do it in one pass.
     (define rec-addresses
       (if current-variant (hash-ref rec-addrs current-variant ∅) ∅))
     (cond
      [(set-member? rec-addresses (reverse rev-addr))
       (define address-var (gensym))
       (define-values (pat* store-updates store*)
         (check-and-rewrite-rhs rhs #f store rev-addr '()))
       (define store** (gensym 'σ))
       (values (Rvar address-var)
               (append store-updates
                       (list (EBinding (Bvar address-var #f)
                                       (Alloc (cons rule-name (reverse rev-addr))))
                             (EBinding (Bvar store** #f)
                                       (Map-extend store* (Rvar address-var) pat*)))))]
      [else
       (match rhs
         [(Bvar x _) (error 'abstract-rule "Rule RHS may not bind ~a" rhs)]
         [(Variant vname pats)
          ;; TODO?: error/warn if space defining vname is trusted.
          (define-values (pats* store-updates store*)
            (let rewrite-pats ([pats pats]
                              [i 0]
                              [store store]
                              [rev-pats* '()]
                              [rev-store-updates '()])
              (match pats
                ['() (values (reverse rev-pats*) (reverse rev-store-updates) store)]
                [(cons pat pats)
                 (define vfield (Variant-field vname i))
                 (define-values (pat* store-updates* store*)
                   (check-and-rewrite-rhs pat vname store
                                          (cons vfield rev-addr)
                                          (list vfield)))
                 (rewrite-pats pats (add1 i) store* (cons pat* rev-pats*)
                               (append (reverse store-updates*) rev-store-updates))])))
          (values (Variant vname pats*) store-updates store*)]
         [other (values other '() store)])])))

  ;; Now we rewrite the LHS to non-deterministically choose values when it
  ;; pattern matches on recursive positions.
  (define-values (lhs* lhs-binding-side-conditions)
    (flatten-pattern lhs '() #f))

  ;; TODO: Finally we rewrite the binding side-conditionts to go between the
  ;; lhs and rhs bindings/side-conditions
  (define binding-side-conditions*
    binding-side-conditions)

  (Rule rule-name lhs* rhs* (append lhs-binding-side-conditions
                                    binding-side-conditions*
                                    store-updates)))

(module+ test
  (require "AAM-concrete.rkt")
  (define CESK-lang
    (Language
     'LC/CESK
     (hash
      'Variable (External-Space symbol? (λ (e) 1) #f)
      'Env (User-Space (list (Map (Space-reference 'Variable) (Address-Space))) #f)
      'Expr (User-Space (list (Variant 'Ref (list (Space-reference 'Variable)))
                              (Variant 'App (list (Space-reference 'Expr)
                                                  (Space-reference 'Expr)))
                              (Space-reference 'Pre-value))
                        #t)
      'Pre-value (User-Space (list (Variant 'Lam (list (Space-reference 'Variable)
                                                       (Space-reference 'Expr))))
                             #t)
      'Value (User-Space (list (Variant 'Closure
                                        (list (Space-reference 'Pre-value)
                                              (Space-reference 'Env))))
                         #f)
      'Frame (User-Space (list (Variant 'Ar (list (Space-reference 'Expr) (Space-reference 'Env)))) #f)
      'Store (User-Space (list (Map (Address-Space) (Space-reference 'Value))) #f)
      'Kont (User-Space (list (Variant 'mt '())
                              (Variant 'Kcons (list (Space-reference 'Frame)
                                                    (Space-reference 'Kont))))
                        #f))))

  (define (Avar x) (Bvar x #f))
  (define CESK-reduction
    (list
     (Rule 'variable-lookup
           (Variant 'State
                    (list
                     (Variant 'Closure (list (Variant 'Ref (list (Avar 'x)))
                                             (Avar 'ρ)))
                     (Avar 'σ)
                     (Avar 'κ)))
           (Variant 'State
                    (list (Rvar 'v)
                          (Rvar 'σ)
                          (Rvar 'κ)))
           (list (EBinding (Avar 'v) (Map-lookup* 'σ (Map-lookup 'ρ (Rvar 'x) #f #f) #f #f))))
     (Rule 'application
           (Variant 'State
                    (list
                     (Variant 'Closure (list (Variant 'App (list (Avar 'e0) (Avar 'e1)))
                                             (Avar 'ρ)))
                     (Avar 'σ)
                     (Avar 'κ)))
           (Variant 'State
                    (list (Variant 'Closure (list (Rvar 'e0) (Rvar 'ρ)))
                          (Rvar 'σ)
                          (Variant 'Kcons
                                   (list (Variant 'Ar (list (Rvar 'e1) (Rvar 'ρ)))
                                         (Rvar 'κ)))))
           '())
     (Rule 'argument-eval
           (Variant 'State
                    (list (Bvar 'v 'Value) (Avar 'σ)
                          (Variant 'Kcons (list (Variant 'Ar (list (Avar 'e) (Avar 'ρ)))
                                                (Avar 'κ)))))
           (Variant 'State
                    (list (Variant 'Closure (list (Rvar 'e) (Rvar 'ρ)))
                          (Rvar 'σ)
                          (Variant 'Kcons (list (Variant 'Fn (list (Rvar 'v)))
                                                (Rvar 'κ)))))
           '())
     (Rule 'function-eval
           (Variant 'State
                    (list (Bvar 'v 'Value) (Avar 'σ)
                          (Variant 'Kcons
                                   (list (Variant 'Fn
                                                  (list (Variant 'Closure
                                                                 (list (Variant 'Lam (list (Avar 'x) (Avar 'e)))
                                                                       (Avar 'ρ)))))
                                         (Avar 'κ)))))
           (Variant 'State
                    (list (Variant 'Closure (list (Rvar 'e) (Rvar 'ρ*)))
                          (Rvar 'σ*)
                          (Rvar 'κ)))
           (list (EBinding (Avar 'a) (Alloc (list 'function-eval 'x)))
                 (EBinding (Avar 'ρ*) (Map-extend 'ρ (Rvar 'x) (Rvar 'a) #f))
                 (EBinding (Avar 'σ*) (Map-extend 'σ (Rvar 'a) (Rvar 'v) #f))))))

  (let-values ([(abs-lang rec-addrs abstract-spaces) (abstract-language CESK-lang)])
    (pretty-print abs-lang)
    (pretty-print rec-addrs)
    (pretty-print abstract-spaces)
    (when #f
      (pretty-print (for/list ([rule (in-list CESK-reduction)])
                      (abstract-rule abs-lang rec-addrs 'σ rule))))
    (when #t
      (pretty-print (abstract-rule abs-lang rec-addrs 'σ (rule-lookup CESK-reduction 'argument-eval)))))

  (define (inject L e)
    (define term (sexp-to-dpattern/check e 'Expr L))
    (Variant 'State (list (Variant 'Closure (list term #hash()))
                          #hash()
                          (Variant 'mt '()))))
  (define (run L expr)
    (c/apply-reduction-relation* CESK-lang CESK-reduction (inject L expr) #hash()))

  (run CESK-lang '(App (Lam x (Ref x))
                       (Lam y (Ref y)))))

;; [1] Might and Shivers ICFP 2006 "Improving flow analyses via ΓCFA: Abstract garbage collection and counting"