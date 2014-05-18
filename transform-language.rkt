#lang racket/base

(require graph
         racket/trace racket/dict racket/match racket/set
         (only-in "lattices.rkt" pc⊔ for/pc⊔)
         "spaces.rkt"
         "shared.rkt")
(provide abstract-language
         external-recursion?
         replace-recursive-mentions)

(define (external-recursion? spaces S)
  (match S
    [(or (? Address-Space?) (? External-Space?) (? Datum?))
     #t]
    [(or (Map _ ex? _ _) (℘ _ ex? _)) ex?]
    [(or (Space-reference _ _ _ name)
         (? symbol? name))
     (external-recursion? spaces (hash-ref spaces name))]
    [(User-Space C _ _) (external-recursion? spaces C)]
    [_ #f]))

;; language-recursive-spaces : Map[Space-name,Space] → Map[Space-name,Set[Space-Name]]
;; Map space names to set of space names that are mutually recursive with them.
;; Examples: List[A] = nil | (Cons A List[A]) ==> 'List |-> (set 'List)
;;           S-exp[A] = A | S-exps[A]
;;           S-exps[A] = nil | (Cons S-exp[A] S-exps[A]) ==> ['S-exp |-> #0=(set 'S-exp 'S-exps), 'S-exps |-> #0#]
;; NOTE: a space without Variants is not recursive since the recursion gets externalized.
(define (language-recursive-spaces/aliases Lspaces)
  (define LG (language-spaces->graph Lspaces))
  ;; Do a little error checking while discovering recursion.
  (define recursive-islands (scc LG))
  ;; Make a map of Space-name to Set[spaces recursive with Space]
  (for/fold ([rec ρ₀] [alias ∅])
      ([cc (in-list recursive-islands)]
       #:unless (match cc
                  ;; The reference nodes themselves are administrative.
                  [(list (? Space-ref-node?)) #t] [_ #f]))
    ;; each space is recursive with each ref'd space.
    (define-values (spaces aliases)
      (for*/fold ([spaces ∅] [aliases ∅])
          ([c (in-list cc)]
           #:when (Space-ref-node? c)
           [sn (in-value (Space-ref-node-sn c))])
        (define name (Space-node-name sn))
        (if (external-recursion? Lspaces name)
            (values spaces (set-add aliases name))
            (values (set-add spaces sn) aliases))))
    ;; Don't record recursive relationships with trusted recursive spaces.
    (define space-names
      (for/set ([space (in-set spaces)]
                #:unless (Space-node-trust-rec space)) (Space-node-name space)))
    (define-values (rec* dummy0 dummy1)
      (for/fold ([rec rec] [trust-rec -unmapped] [trust-con -unmapped])
          ([space (in-set spaces)])
        (match-define (Space-node _ ctrust-rec ctrust-con) space)
        (cond [(and (or (eq? trust-rec -unmapped) (equal? trust-rec ctrust-rec))
                    (or (eq? trust-con -unmapped) (equal? trust-con ctrust-con)))
               (define name (Space-node-name space))
               (values (hash-set rec name space-names)
                       ctrust-rec
                       ctrust-con)]
              [else
               (error 'bad-trust "Recursive spaces have mismatched recursion trust ~a" cc)])))
      (values rec* (set-union alias aliases))))

(define (language-abstract-spaces-and-recursive-positions options spaces recursive-spaces aliases)
  ;; Seed the abstract space map with defaults we know.
  (define abstract-spaces₀
    (for/fold ([h ρ₀]) ([(name space) (in-dict spaces)])
      (match space
        [(? External-Space?)
         (hash-set h name (External-Space-precision space))]
        [(User-Space (Address-Space _ _ equal-behavior) _ _)
         (hash-set h name (match equal-behavior
                            ['Identity 'discrete]
                            ['Deref 'abstract]))]
        ;; User spaces with trusted recursion still might be composed of untrusted spaces.
        ;; Thus when hitting a reference with trusted recursion, we do nothing to the abstraction.
        ;; If not trusted, we join with the abstraction of the address space.
        ;; Start at bottom to move higher if necessary.
        [_ (hash-set h name 'concrete)])))

  (define frm
    (find-recursive-mentions options spaces recursive-spaces aliases))
  ;; Find all recursive addresses and build the first pass of abstract-spaces.
  (define-values (variant-rec-addrs abstract-spaces₁)
    (for/fold ([rec-addrs ρ₀] [abstract-spaces abstract-spaces₀])
        ([(name space) (in-dict spaces)])
      (frm rec-addrs abstract-spaces name space)))
  ;; All spaces should have precision classifications.
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
;; Returns (1) a language that cuts all untrusted non-externalized recursion out into addresses,
;; (2) a map from variants to positions of self-reference (and mutually-recursive references),
;; (3) a map from space names to their precision classifier
(define (abstract-language L [in-options #f])
  ;; We first turn L into a graph in the following way:
  ;; External spaces and (Address-Space) are terminal nodes (no outgoing edges).
  ;; Space names are nodes that point to all of their variant nodes' Variant-Addresses
  ;; (Space-reference name) is treated as the node for name.

  ;; All space names (S) that are in the same strongly connected component are treated as
  ;; recursive. That is, for the Variants-or-Components in S, any (Space-reference name) is
  ;; replaced by (Address-Space) when name ∈ S, and the address of the position is added to
  ;; the recursive mention map.

  (match-define (Language spaces refinement-order loptions) L)
  (define options (or in-options loptions))
  (define-values (recursive-spaces aliases)
    (language-recursive-spaces/aliases spaces))
  (define nonrec-spaces
    (for/set ([(name space) (in-dict spaces)]
              #:when (external-recursion? spaces space))
      name))
  (define-values (abstract-spaces variant-rec-addrs)
    (language-abstract-spaces-and-recursive-positions options spaces recursive-spaces aliases))

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

           [(User-Space c trust-recursion? trust-construction?)
            (define abs-variants
              ((replace-recursive-mentions options nonrec-spaces recursive-spaces name) c))
            ;; NOTE: trusted recursion is not rewritten since it is not
            ;; represented in recursive-spaces
            (User-Space abs-variants trust-recursion? trust-construction?)]))

       (hash-set abs-spaces name abs-space)))

   (Abs-Language
    (Language abs-spaces refinement-order options)
    variant-rec-addrs
    recursive-spaces
    abstract-spaces
    nonrec-spaces))

;; replace-recursive-mentions : Options Lang-spaces Space-name (∪ Variant Component) → (∪ Variant Component)
;; With abstract spaces and recursive spaces computed, we can lift abstract maps to powerset codomain,
;; and replace spaces in recursive positions with (Address-Space)
(define (replace-recursive-mentions options nonrec-spaces recursive-spaces current-space)
  (define (replace-recursive-mentions-in-component comp)
       (match comp
         [(Space-reference _ emb eeb name)
          (define name (Space-reference-name comp))
          (if (and (set-member? (hash-ref recursive-spaces current-space ∅) name)
                   (not (set-member? nonrec-spaces name)))
              (Address-Space 'AAM
                             (or emb
                                 (Options-match-default options)
                                 core-match-default)
                             (or eeb
                                 (Options-equal-default options)
                                 core-equal-default))
              ;; Non-recursive references are not replaced, even if the spaces are abstract.
              comp)]
         ;; NOTE: sets and maps not under names are always externalized.
         [(℘ _ ex comp)
          (define abs-comp (replace-recursive-mentions-in-component comp))
          (℘ (Component-pc abs-comp) ex abs-comp)]
         [(Map _ ex domain range)
          (define abs-dom
            (replace-recursive-mentions-in-component domain))
          (define abs-rng
            (replace-recursive-mentions-in-component range))
          (define dom-pc (Component-pc abs-dom))
          (define rng-pc (Component-pc abs-rng))
          ;; If a map domain contains addresses, the map is now treated as
          ;; m(a) = b implies ∃ A ∈ γ(a). A ↦ b, but we don't know if A is actually in the map.
          ;; Additionally, the Map now becomes weak, so b is lifted implicitly to a powerset domain.
          (cond [(eq? dom-pc 'concrete)
                 (Map rng-pc ex abs-dom abs-rng)]
                [else 
                 (Map (pc⊔ dom-pc rng-pc) ex abs-dom (℘ rng-pc ex abs-rng))])]
         [(Variant pc name comps tr tc)
          (define abs-comps
            (for/vector #:length (vector-length comps)
                        ([comp (in-vector comps)])
                        (replace-recursive-mentions-in-component comp)))
          (Variant (for/pc⊔ ([c (in-vector abs-comps)])
                            (Component-pc c))
                   name abs-comps tr tc)]
         [(∪ _ comps)
          (define-values (pc rev-comps)
            (for/fold ([pc 'concrete] [rev-comps '()])
                ([c (in-list comps)])
              (define c* (replace-recursive-mentions-in-component c))
              (values (pc⊔ (Component-pc c*) pc) (cons c* rev-comps))))
          (∪ pc (reverse rev-comps))]

         [_ comp]))
  replace-recursive-mentions-in-component)

(define (hash-pc⊔ h k v)
  (hash-set h k (pc⊔ v (hash-ref h k 'concrete))))

(define (find-recursive-mentions options spaces recursive-spaces aliases)
  (define (self rec-addrs abstract-spaces current-space space [rev-addr (list current-space)] [local-rev-addr '()])
    ;; find-recursive-mentions :
    ;;  Map[Space-name,Set[Space-name]] Space-name 
    ;;  Space Map[(∪ Variant-Address Variant-name),Variant-Address] Rec-Space-Map →
    ;;    (values Map[Variant-name,Variant-Address] Rec-Space-Map)
    ;; Where Rec-Space-Map = Map[Space-name,(∪ Set[Space-name] Boolean)]
    ;; Purpose:
    ;; Build a map of ((path to enclosing variant) or variant name) to
    ;;                relative addresses of recursive space references,
    ;; and a map of Space-name to Precision-Classifier or a set of spaces
    ;;   which bound below the classification of the space.
    ;; All mutual dependencies are trusted, meaning their references' classification is 'concrete.

    ;; Get the set of recursive mentions and fill out abstract-space dependencies.
    (define (find-recursive-mentions-in-component comp rev-addr local-rev-addr rec-addrs abs-spaces)
      (define (simple-name name)
        (values rec-addrs
                (match (hash-ref abs-spaces name ∅)
                  ['concrete abs-spaces] ;; known non-recursive
                  [(? symbol? pc)        ;;(or 'abstract 'discrete)
                   (hash-pc⊔ abs-spaces current-space pc)]
                  ;; unknown. Add to set of names to resolve after finishing.
                  [dependents
                   (cond
                    [(symbol? (hash-ref abs-spaces current-space -unmapped))
                     ;; Already showed current-space is abstract for a different reason.
                     ;; We don't know more about name here.
                     abs-spaces]
                    [(set? dependents)
                     ;; If name is abstract, then so is current-space.
                     (hash-join abs-spaces current-space (set-add dependents name))]
                    [else (error 'find-recursive-mentions-in-component
                                 "INTERNAL: expected boolean or set: ~v" dependents)])])))

      (match comp
        [(? Space-reference?)
         (define name (Space-reference-name comp))
         (cond
          [(set-member? aliases name)
           (self
            rec-addrs abs-spaces current-space (hash-ref spaces name) rev-addr local-rev-addr)]
          [(set-member? (hash-ref recursive-spaces current-space ∅) name)
           (values (hash-add rec-addrs rev-addr (reverse local-rev-addr))
                   ;; The current space is at least as abstract as the expected replacement address.
                   (hash-pc⊔ abs-spaces current-space
                             (match (or (Space-reference-expected-equal-behavior comp)
                                        (Options-equal-default options)
                                        core-equal-default)
                               ['Identity 'discrete]
                               ['Deref 'abstract])))]
          [else (simple-name name)])]
        [(℘ pc ex comp)
         (find-recursive-mentions-in-component
          comp rev-addr (cons '℘ local-rev-addr) rec-addrs abs-spaces)]
        [(Map pc ex domain range)
         (define-values (rec-addrs* abs-spaces*)
           (find-recursive-mentions-in-component
            domain rev-addr (cons 'domain local-rev-addr) rec-addrs abs-spaces))
         (find-recursive-mentions-in-component
            range rev-addr (cons 'range local-rev-addr) rec-addrs* abs-spaces*)]
        [(Address-Space _ _ equal-behavior)
         (values rec-addrs (hash-pc⊔ abs-spaces current-space (match equal-behavior
                                                                ['Identity 'discrete]
                                                                ['Deref 'abstract])))]
        [(Variant pc name comps tr tc)
         (define here (cons name (append local-rev-addr rev-addr)))
         (for/fold ([rec-addrs* rec-addrs] [abs-spaces* abs-spaces])
             ([comp (in-vector comps)]
              [i (in-naturals)])
           (define-values (rec-addrs** abs-spaces**)
             (find-recursive-mentions-in-component
              ;; XXX: restarting rev-addr
              comp here (list (Variant-field name i))
              rec-addrs* abs-spaces*))
           ;; NOTE: all the relative addresses from here that are not under
           ;; yet another variant will be mapped to @racket[here].
           (define addrs (hash-ref rec-addrs** here ∅))
           (values (hash-set rec-addrs** name addrs)
                   abs-spaces**))]
        ;; A recursive mention not under a variant must be under a map.
        ;; Maps are ensured finite by the rest of the abstraction process.
        [(∪ pc comps)
         (for/fold ([rec-addrs rec-addrs]
                    [abs-spaces abstract-spaces])
             ([c (in-list comps)])
           ;; XXX: this assumes that addresses into ∪ are unique without extra
           ;; direction. This needs to be ensured by the parser.
           (find-recursive-mentions-in-component
            c rev-addr local-rev-addr rec-addrs abs-spaces))]
        [(? terminal-component?) (values rec-addrs abs-spaces)]))

    (match space
      ;; already set abstract-spaces and no new rec-addrs.
      [(or (? External-Space?) (? Address-Space?))
       (values rec-addrs abstract-spaces)]
      [(User-Space component trust-recursion? trust-construction?)
       (define-values (rec-addrs* abstract-spaces*)
         (find-recursive-mentions-in-component
          component rev-addr '() rec-addrs abstract-spaces))
       (cond
        [trust-recursion?
         ;; All variants are mapped to ∅ to drive later "recursive replacements" to leave
         ;; trusted spaces alone.
         (values
          (let variant->empty ([c component] [rec-addrs rec-addrs])
            (define (forall seq rec-addrs)
              (for/fold ([rec-addrs rec-addrs]) ([x seq])
                (variant->empty x rec-addrs)))
            (match c
              [(? Variant?)
               (forall (in-vector (Variant-Components c))
                       (hash-set rec-addrs (Variant-name c) ∅))]
              [(Map _ _ k v)
               (variant->empty v (variant->empty k rec-addrs))]
              [(℘ _ _ c)
               (variant->empty c rec-addrs)]
              [(∪ _ cs) (forall (in-list cs) rec-addrs)]
              [_ rec-addrs]))
          abstract-spaces*)]
        [else (values rec-addrs* abstract-spaces*)])]))
  self)

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
        [(? symbol? pc) (values abs-spaces pc)]
        [deps
         (define-values (abs-spaces* pc)
           (for/fold ([h abs-spaces] [pc 'concrete])
               ([dep (in-set deps)])
             (define-values (h* pc*) (loop h dep))
             (values h* (pc⊔ pc pc*))))
         (values (hash-set abs-spaces* space-name* pc) pc)])))
  abs-spaces*)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Graph code
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

(define (component->endpoints comp rev-addr)
  (match comp
    [(? Space-reference?)
     (set (Endpoint (reverse rev-addr)
                    (Space-reference-name comp)))]
    [(℘ pc ex comp) (component->endpoints comp (cons '℘ rev-addr))]
    [(Map pc ex domain range)
     (set-union (component->endpoints domain (cons 'domain rev-addr))
                (component->endpoints range (cons 'range rev-addr)))]
    [(∪ pc comps)
     (for/union ([c (in-list comps)])
       (component->endpoints c rev-addr))]
    [(Variant pc name comps tr tc)
     (for/fold ([acc ∅]) ([comp (in-vector comps)]
                          [i (in-naturals)])
       ;; XXX: we use local addresses for variants
       (for/fold ([acc acc]) ([endpoint (in-set (component->endpoints comp '()))])
         (match-define (Endpoint addr space) endpoint)
         (set-add acc (Endpoint (cons (Variant-field name i) addr) space))))]
    [(? terminal-component?) (set (Endpoint (reverse rev-addr) comp))]
    [_ (error 'component->endpoints "INTERNAL: Bad component ~a" comp)]))

;; Spaces are represented as Space-node to do error-checking.
;; If two spaces with different trusted? booleans appear in the same scc, error.
(define (add-space-nodes! G spaces)
  (for/fold ([h ρ₀]) ([(name space) (in-dict spaces)])
    (hash-set h name
              (match space
                [(? External-Space?)
                 (unless (has-vertex? G space) (add-vertex! G space))
                 space]
                [(User-Space _ trust-recursion? trust-construction?)
                 (define node (Space-node name trust-recursion? trust-construction?))
                 (define self-node (Space-ref-node node))
                 (unless (has-vertex? G node)
                   (add-vertex! G node)
                   (add-vertex! G self-node)
                   (add-directed-edge! G self-node node))
                 node]))))

(define (add-space-edges! G Space-nodes name space)
  (match space
    [(User-Space component trust-recursion? trust-construction?)
     (define node (hash-ref Space-nodes name))
     (for* ([endpoint (in-set (component->endpoints component (list name)))])
       (match-define (Endpoint addr space) endpoint)
       (define space-node
         (cond
          [(terminal-component? space) space]
          [(symbol? space)
           (match (hash-ref Space-nodes space
                            (λ () (error 'add-space-edges!
                                         "Space ~a refers to unknown space ~a" name space)))
             [(? Space-node? sn) (Space-ref-node sn)]
             [other other])]
          [else (error 'add-space-edges! "INTERNAL: Bad endpoint space ~a" space)]))
       (add-directed-edge! G node addr)
       (add-directed-edge! G addr space-node))]
    [_ (void)]))

