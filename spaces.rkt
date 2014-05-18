#lang racket/base

(require racket/set (for-syntax racket/base) racket/fixnum racket/list
         racket/match)
(provide (struct-out Language)
         (struct-out Abs-Language)

         (struct-out Component)
         (struct-out Address-Space)
         (struct-out Space-reference)
         Bool Bool? -Bool
         (struct-out Map)
         (struct-out ℘)
         (struct-out ∪)
         (struct-out Variant)
         (struct-out Anything*)
         Anything? -Anything
         Component-pc
         terminal-component?

         (struct-out ffun)
         (struct-out fset)
         (struct-out variant)
         (struct-out Address)
         (struct-out external) -⊤
         user-set? mk-user-set make-immutable-user-set u∅

         (struct-out User-Space)
         (struct-out External-Space)

         (struct-out State) mk-State
         (struct-out Abs-State) mk-Abs-State

         pure many allocs alloc/many
         writes write/many write/alloc write/alloc/many
         reads read/many read/alloc read/alloc/many
         read/write read/write/many read/write/alloc read/write/alloc/many
         reads? writes? allocs? many? add-reads add-writes add-allocs add-many

         (struct-out BSCS)
         (struct-out Store-extend)
         (struct-out When)
         (struct-out Binding)

         (struct-out expression) no-comp-yet
         (struct-out Term)
         (struct-out Store-lookup)
         (struct-out Meta-function-call)
         (struct-out If)
         (struct-out Equal)
         (struct-out Let)
         (struct-out Match)
         (struct-out Choose)
         (struct-out Alloc)
         ;; map-expressions
         (struct-out Map-empty?)
         (struct-out Empty-map)
         (struct-out Map-lookup)
         (struct-out Map-extend)
         (struct-out Map-remove)
         (struct-out In-Dom?)
         ;; set-expressions
         (struct-out Set-empty?)
         (struct-out Empty-set)
         (struct-out In-Set?)
         (struct-out Set-Union)
         (struct-out Set-Intersect)
         (struct-out Set-Subtract)
         (struct-out Set-Remove*)
         (struct-out Set-Add*)
         ;; unsafe expressions
         (struct-out Unsafe-store-space-ref)
         (struct-out Unsafe-store-ref)
         (struct-out ???)

         (struct-out Name)
         (struct-out is-a)
         (struct-out Map-with)
         (struct-out Set-with)
         (struct-out Rvar)
         (struct-out Datum)

         (struct-out Abs-Result/effect)
         (struct-out Choice)
         (struct-out Abs-Data)

         (struct-out Rule)
         (struct-out Reduction-Relation)
         (struct-out Meta-function)

         ρ₀ ∅
         -unmapped
         debug-mode

         ;; for transformation
         (struct-out Variant-field)
         (struct-out Space-component)

         ;; for parsing
         (struct-out with-orig-stx)
         (struct-out Options)
         core-match-default
         core-equal-default
         core-externalize-default
         core-pun-spaces-default
         core-raise-type-errors-default
         core-error-on-missing-expect-default)
#|
Allow spaces to be inductively defined or provided with the promise that they are finite
Allow powerset constructor
Allow functions
Allow stores (special)

|#

;; A Language is a (Language Name Map[Space-name,Either[Space,Component]])
;; Where scope of space names is letrec*
;; All occurrences of the same named Variant are expected to have a total ordering.
;;   That is, some spaces may use a refined notion of a variant, but never a re-defined notion.
(struct Language (spaces refinement-order options) #:transparent)
(struct Abs-Language (L recursive-addresses recursive-spaces abstract-spaces nonrec-spaces)
        #:transparent)

;; TODO list for Language sanity checking:
;; - DONE (abstract-language): check for undefined spaces
;; - check for unguarded recursion
;; - check for contradictory Variant declarations
;; - DONE (abstract-language): check that mutually-recursive spaces that declare
;;                             trust-recursion anywhere declare it everywhere

;; A Space is a (Space Symbol List[Variant] Boolean)
;; where the Boolean declares the space as trusted to be bounded even if recursive.

;; A Component is one of
;; - a (Space-reference Option[Match-Behavior] Option[Equal-Behavior] Name)
;; - an (Address-Space Name Match-Behavior Equal-Behavior)
;; - a (Map Boolean Component Component)
;; - a (℘ Component)
;; - a (Variant Name Vector[Component] Boolean Boolean)
;; - (Anything)
;; - a (Datum atom)
;; The Anything variant is special. It stands for a /trusted/ "Any" pattern.
;; TODO: allow Anything* to be a component for debugging purposes
;; TODO: Add a WeakMap option for automatic GC.

(struct Component (precision-classifier) #:transparent)
(struct Space-reference Component (expected-match-behavior expected-equal-behavior name)
        #:transparent)
(struct Bool () #:transparent) (define -Bool (Bool))
(struct Map Component (externalize? domain range) #:transparent)
(struct ℘ Component (externalize? component) #:transparent)
(struct ∪ Component (comps) #:transparent)
;; tr and tc get distributed from User-Space declaration for easy access in transformation.
(struct Variant Component (name Components trust-recursion? trust-construction?) #:transparent)
;; no checking actually necessary, but check if in debug mode
(struct Anything* (debug-component) #:transparent)
(struct Anything () #:transparent) (define -Anything (Anything)) ;; UNSAFE COMPONENT
(define (Component-pc c)
  (match c
    [(Component pc) pc]
    [(or (? Datum?) (? Bool?)) 'concrete]
    [(Address-Space _ _ equal-behavior)
     (match equal-behavior
       ['Identity 'discrete]
       ['Deref 'abstract])]
    [(Anything* c) (Component-pc c)]
    [(? Anything?) 'abstract]))
(define (terminal-component? c) ;; (not (Component? c)) also holds
  (or (Address-Space? c) (Datum? c) (Bool? c) (boolean? c) (Anything? c) (Anything*? c)))

(struct ffun (mcomp dict) #:transparent)
(struct fset (scomp set) #:transparent)

;; TODO?: allow variants or components to have side-conditions
;; Elements of Variant contain a pointer to the type of the variant.
(struct variant (vpointer data) #:transparent)

;; elements of ℘ are hash sets, but abstract combinations are user-sets.
(define-custom-set-types user-set equal?)
(define (mk-user-set . rest) (make-immutable-user-set rest))
(define u∅ (mk-user-set))
;; Addresses specify which address space they are in, for store separation purposes.
;; Addresses have specified match behavior and equality-checking behavior.
;; A Match-Behavior is one of
;; - 'Choose on match [eager non-determinism]
;; - 'Deref on match [lazy non-determinism without delayed lookup]
;; - 'Delay on match [lazy non-determinism with delayed lookup]

;; An Equal-Behavior is one of
;; - 'Deref [structural equality, allowed to compare with non-addresses, but addresses get μ check]
;; - 'Identity [egal equality: pointers must be the same, and μ = 1 means Must equal o.w. May]
(struct Address (space addr match-behavior equal-behavior) #:transparent)

;; A store is a map from Address to (Space-ref Name).
;; store-spaces is a Map[Address-Space-Name,Store]
;; OPT-OP: precalculate address spaces names and translate to numbers to use vectors instead of hashes.
(struct State (term store-spaces) #:transparent)
;; Create an initial state
(define (mk-State tm) (State tm #hash()))

(struct Abs-State (term σ μ τ̂) #:transparent)
(define (mk-Abs-State tm τ̂₀) (Abs-State tm #hash() #hash() τ̂₀))

;; A Precision-Classifier is one of
;; - 'concrete [and thus discrete]
;; - 'discrete-abstraction [considered abstract, but still gets structural equality]
;; - 'abstract [must use slow-path equality checks]

;; A Card is one of
;; - 0
;; - 1
;; - 'ω

;; A Boolean♯ is one of
;; - #t
;; - #f
;; - 'b.⊤

;; A Space is one of
;; - (User-Space Component Boolean Boolean)
;; - (External-Space (Any → Boolean) (Any [Addr ↦ Card] → Card) Precision-Classifier
;;                   (Any Any Store-Spaces Card-map equality-map → Boolean♯)
;; - (Address-Space)
;; An external space has a predicate that decides membership,
;; a cardinality analysis for values of the space (may be given the abstract count [1] map), and
;; a precision-classifier that is 'concrete if the cardinality analysis is always 1,
;; an optional (Any Any [Addr ↦ Card] → Boolean♯) that quasi-decides equality given count info.
;;  NOTE: if not given, equality falls back on structural equality plus cardinality analysis.
;;
;; A user space may not have duplicate variants.
(struct User-Space (component trust-recursion? trust-construction?) #:transparent)
(struct Address-Space (space match-behavior equal-behavior) #:transparent)
(struct External-Space (pred cardinality precision ≡ ⊔ enum quine) #:transparent) ;;⊑ ??

;; A member of an External space is one of
;; - (external external-space Any)
;; - Any [such that the pred of some external space in the language is satisfied]
(struct external (space v) #:transparent)
(struct ⊤ () #:transparent) (define -⊤ (⊤))

;; A rule is a (Rule Any Pattern Pattern List[Either[Binding,Side-condition]] Store-Interaction)
;; A Rule name is used for guiding allocation.

(struct Rule (name lhs rhs binding-side-conditions left-expect right-expect) #:transparent)
(struct Reduction-Relation (rules state-expect) #:transparent)

;; A Pattern is one of
;; - a (is-a Component)
;; - a (Name Symbol Pattern)
;; - an (Rvar Symbol)
;; - a (Datum Literal-data)
;; - a (variant Variant Immutable-Vector[Pattern]) [morally]
;; - a (Set-with Pattern Pattern Match-mode Map) [for structural termination arguments]
;; - a (Map-with Pattern Pattern Pattern Match-mode Set) [for structural termination arguments]
;;   XXX: how to handle May-present entries?
;; - an atom
;; Name patterns bind on the left if not already mapped.
;; If mapped, an equality check occurs before matching continues.
;; If a Space name is specified, matching ensures the value fits in the space expected.
;; An Rvar refers to a pattern variable in scope.
;; NOTE: If the variable is mapped, an equality check will occur without checking
;;       if the value is in the specified Space (it is assumed to succeed).
;; NOTE: I say morally for immutable, since Racket doesn't have the best support for immutable vectors.
;;       We use standard vectors.
;; Map-with and Set-with contain pointers to the Map and ℘ components respectively
;; for effective transformation.

;; A Match-mode is one of
;; - 'any {anything that completely matches, regardless of quality}
;; - 'all {all matches}
;; - 'best {a match with the highest quality possible with the patterns}
(struct Name (x pat) #:transparent)
(struct is-a (c) #:transparent)
(struct Map-with (kp vp mp mode mpointer) #:transparent)
(struct Set-with (vp sp mode spointer) #:transparent)
(struct Rvar (x) #:transparent)
(struct Datum (d) #:transparent)

(define ρ₀ (hash))
(define ∅ (set))

;; A DPattern (or "data pattern") is either
;; - a  (variant Variant Immutable-Vector[DPattern]) [morally]
;; - an (Address _ _ _ _)
;; - an (fset Component Abs-Data)
;; - an (fmap Component Component Map[DPattern,DPattern])
;; - a (Datum atom)

;; An Abs-Data is an (Abs-Data Map[External-Space,external] Set[DPattern])
(struct Abs-Data (externals data) #:transparent)
(struct Choice (label data) #:transparent)

(struct Binding (lhs rexpr) #:transparent)
(struct When (expr) #:transparent)
;; Make a syntactic distinction between allocations that expect to have
;; structural equality (SAlloc) or Egal/Mutable equality (MAlloc)

;; OPT-OP: allow specialized Store-extend and Alloc forms that know statically
;;         which address space they're using/producing addresses from/to
;; By treating store extensions as bindings, we can control the store flow.
;; We also don't need to make intermediate store names, which is a plus.

;; OPT: classifying expressions with their store interaction allows us to have better
;; allocation strategies when evaluating expressions.
;; If an expression only needs to write to the store, we can output deltas;
;; if only read, the output does not need to allocate for multiple returns;
;; if only alloc, then we only need to change the abstract count, but not the store;
;; and any combinations thereof. It can be advantageous to memoize expressions that do not read the store.
;; A Store-Interation is a combination of
;; - read        (10000b)
;; - write       (01000b)
;; *** cardinality (00100b) *** REMOVED, since we don't know if we need to read through store.
;; - alloc       (00010b)
;; - many        (00001b)
;; All encoded as a 4 bit number (fixnum)
(define-values
  (pure many allocs alloc/many
   writes write/many write/alloc write/alloc/many
   reads read/many read/alloc read/alloc/many
   read/write read/write/many read/write/alloc read/write/alloc/many)
  (apply values (range 16)))

(define (reads? n) (not (eq? 0 (fxand n reads))))
(define (writes? n) (not (eq? 0 (fxand n writes))))
(define (allocs? n) (not (eq? 0 (fxand n allocs))))
(define (many? n) (not (eq? 0 (fxand n many))))

(define (add-reads n) (fxior n reads))
(define (add-writes n) (fxior n writes))
(define (add-allocs n) (fxior n allocs))
(define (add-many n) (fxior n many))

(struct expression (store-interaction comp) #:transparent)
(define no-comp-yet #f)


;; An Expression is one of
;; - (Term Pattern)
;; - (Store-lookup Expression)
;; - (If Expression Expression Expression)
;; - (Let BSCS Expression)
;; - (Match Expression List[Rule])
;; - (Equal Expression Expression)
;; - (Meta-function-call name Pattern)
;; - (Alloc Symbol Match-Behavior Equal-Behavior _)
;; Map operations
;; - (Map-lookup Symbol Expression Boolean Expression)
;; - (Map-extend Symbol Expression Expression Boolean)
;; - (Map-remove Symbol Expression)
;; - (Empty-map Component Component) [an empty map of "component" to "component"]
;; - (Map-empty? Symbol)
;; - (In-Dom? Symbol Expression)
;; Set operations
;; - (Empty-set Component) [an empty set of "component"s]
;; - (Set-empty? Expression)
;; - (In-Set? Expression Expression)
;; - (Set-Union Expression List[Expression])
;; - (Set-Add* Expression List[Expression])
;; - (Set-Remove* Expression List[Expression])
;; - (Set-Intersect Expression List[Expression])
;; - (Set-Subtract Expression List[Expression])
(struct Store-extend (key-expr val-expr trust-strong?) #:transparent)

;; Notes: The boolean in Map-extend is whether the map should remain a strong update through abstraction.
;; This only matters for maps that have addresses in their domains.

;; !!!: Opportunity for code reuse: predicative space polymorphism with trust and abstraction kinds.
;; Example: List = ∀ X : (abstract trusted-recursion). '() + (Cons X List[X])
;; Abstraction and trust can also have bounded polymorphism.

(struct Term expression (pat) #:transparent)
(struct Store-lookup expression (key-expr) #:transparent)
(struct Meta-function-call expression (name arg-pat) #:transparent)
(struct If expression (g t e) #:transparent)
(struct Equal expression (l r) #:transparent)
(struct Let expression (bindings body-expr) #:transparent)
  (struct BSCS (store-interaction bindings) #:transparent) ;; non-expression
(struct Match expression (discriminant rules) #:transparent)
;; If expecting a set, make an arbitrary choice.
;; Labelled to distinguish different answers when evaluating expressions.
(struct Choose expression (label expr) #:transparent)

(struct Map-empty? expression (mvar) #:transparent)
(struct Empty-map expression () #:transparent)
(struct Map-lookup expression (mvar key-expr default? def-expr) #:transparent)
(struct Map-extend expression (mvar key-expr val-expr trust-strong?) #:transparent)
(struct Map-remove expression (mvar key-expr) #:transparent) ;; doesn't error if key not present.
(struct In-Dom? expression (mvar key-expr) #:transparent)

(struct Set-empty? expression (expr) #:transparent)
(struct Empty-set expression () #:transparent)
(struct In-Set? expression (set-expr expr) #:transparent)
(struct Set-Union expression (set-expr exprs) #:transparent)
(struct Set-Intersect expression (set-expr exprs) #:transparent)
(struct Set-Subtract expression (set-expr exprs) #:transparent)
(struct Set-Remove* expression (set-expr exprs) #:transparent)
(struct Set-Add* expression (set-expr exprs) #:transparent)


(struct Unsafe-store-space-ref expression () #:transparent)
(struct Unsafe-store-ref expression (space) #:transparent)
(struct ??? expression (label) #:transparent)

(struct Alloc expression (space match-behavior equal-behavior hint) #:transparent)

;; We attach a certainty of a result to qualify if it follows from cumulatively
;; strong or weak side-conditions in Let or top-level forms.
;; certain? is #t if the result can be /reached/ concretely,
;; even if the result may be abstract.
(struct Abs-Result/effect (certain? term store-spaces μ) #:transparent)

;; the definition of a meta-function is like a reduction semantics,
;; but treated like a functional relation.
;; Any use of addresses can lead to non-determinism and several results, but
;; each recursive position of a variant pattern can be labeled with '∀ or '∃ to control
;; in which way evaluation of the meta-function goes.
;; For example, if we have side-conditions checking each element of a list for a property,
;; I can label the rest position as '∀ to ensure every abstract list denotation has the property.
;; I can also use '∃ to make sure at least one list has the property.
;; Further, we allow custom implementations of a meta-function if the specifier wishes for more control.

;; A Meta-function is a
;; (Meta-function Symbol List[Rule] Store-Interaction Option[DPattern → DPattern] Option[DPattern → ℘(DPattern)])
;; The store-interaction is a summary of all the rules' store-interactions.
;; TODO: termination back-door?
(struct Meta-function (name rules store-interaction trusted-implementation/conc trusted-implementation/abs) #:transparent)

;; A unique value to distinguish lookup failures.
(struct Unmapped ()) (define -unmapped (Unmapped))

;; A Component-Address is one of
;; - '℘
;; - 'domain
;; - 'range

;; A Variant-Address is a Pair[Variant-field,List[Component-Address]]
(struct Variant-field (name index) #:transparent)
(struct Space-component (name) #:transparent)

;; An Allocation-Address is a List[(∪ Variant-field Component-Address)]

;; For parsing and transformation
(struct with-orig-stx (v core surface-stx) #:transparent)
(struct Options (pun-space?
                 externalize?
                 raise-type-errors?
                 error-on-missing-expect?
                 match-default
                 equal-default))
(define core-match-default 'Choose)
(define core-equal-default 'Identity)
(define core-externalize-default #t)
(define core-pun-spaces-default #f)
(define core-raise-type-errors-default #t)
(define core-error-on-missing-expect-default #t)

(define debug-mode #f)
