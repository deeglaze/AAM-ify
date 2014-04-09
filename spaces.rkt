#lang racket/base

(require racket/set)
(provide (all-defined-out))
#|
Allow spaces to be inductively defined or provided with the promise that they are finite
Allow powerset constructor
Allow functions
Allow stores (special)

|#

;; A Language is a (Language Name Symbol Map[Space-name,Either[Space,Component]])
;; Where scope of space names is letrec*
;; All occurrences of the same named Variant are expected to have a total ordering.
;;   That is, some spaces may use a refined notion of a variant, but never a re-defined notion.
(struct Language (name spaces) #:transparent)

;; TODO list for Language sanity checking:
;; - DONE (abstract-language): check for undefined spaces
;; - check for unguarded recursion
;; - check for contradictory Variant declarations
;; - DONE (abstract-language): check that mutually-recursive spaces that declare
;;                             trust-recursion anywhere declare it everywhere

;; A Space is a (Space Symbol List[Variant] Boolean)
;; where the Boolean declares the space as trusted to be bounded even if recursive.

;; A Component is one of
;; - a (Space-reference Name)
;; - an (Address-Space Name)
;; - a (Map Component Component)
;; - a (℘ Component)
;; - (Anything)
;; The Anything variant is special. It stands for a /trusted/ "Any" pattern.

;; A Qualified-Component is a Component with QMaps instead of Maps.
;; TODO?: Add a WeakMap option for automatic GC.

(struct Space-reference (name) #:transparent)
(struct Map (domain range) #:transparent)
(struct QMap (domain domain-abstract? range) #:transparent)
(struct ℘ (component) #:transparent)
(struct Anything () #:transparent) (define -Anything (Anything))

;; TODO?: allow variants or components to have side-conditions
(struct Variant (name Components) #:transparent)
;; Addresses specify which address space they are in, for store separation purposes.
;; Addresses are classified as either structural or Egal:
;;  - If Must Egal equal, then Must Structural equal. 
;;    Otherwise, dereference both and check equality of product of values;
;;    if all equalities are Must, the equality is must. If all are #f, then the equality is #f. Otherwise May.
;;  - Addresses are Egal equal if syntactically equal (otherwise #f) and
;     if the address cardinality is 1, Must match, else May match.
(struct Address-Structural (space addr) #:transparent)
(struct Address-Egal (space addr) #:transparent)

;; A store is a map from Address to (Space-ref Name).
;; store-spaces is a Map[Address-Space-Name,Store]
;; OPT-OP: precalculate address spaces names and translate to numbers to use vectors instead of hashes.
(struct State (term store-spaces) #:transparent)
;; Create an initial state
(define (mk-State tm) (State tm #hash()))

(struct Abs-State (term σ μ) #:transparent)
(define (mk-Abs-State tm) (Abs-State tm #hash() #hash()))

;; A Card is one of
;; - 0
;; - 1
;; - 'ω

;; A Boolean♯ is one of
;; - #t
;; - #f
;; - 'b.⊤

;; A Space is one of
;; - (User-Space List[Either[Variant,Component]] Boolean)
;; - (External-Space (Any → Boolean) (Any [Addr ↦ Card] → Card) Boolean)
;; - (Address-Space)
;; An external space has a predicate that decides membership,
;; a cardinality analysis for values of the space (may be given the abstract count [1] map), and
;; a boolean that is #t iff the cardinality analysis is ever not 1,
;; an optional (Any Any [Addr ↦ Card] → Boolean♯) that quasi-decides equality given count info.
;;  NOTE: if not given, equality falls back on structural equality plus cardinality analysis.
;;
;; A user space may not have duplicate variants.
(struct User-Space (variants trust-recursion?) #:transparent)
(struct Address-Space (space) #:transparent)
(struct External-Space (pred cardinality imprecise? special-equality) #:transparent)

;; A reduction semantics is a List[Rule]
;; A rule is a (Rule Any Pattern Pattern List[Either[Binding,Side-condition]])
;; A Rule name is used for guiding allocation.

(struct Rule (name lhs rhs binding-side-conditions) #:transparent)

;; A Pattern is one of
;; - a (Bvar Symbol Option[Space-name])
;; - an (Rvar Symbol)
;; - a (Variant Name Immutable-Vector[Pattern]) (morally)
;; - an atom
;; Bvar patterns bind on the left if not already mapped.
;; If mapped, an equality check occurs before matching continues.
;; If a Space name is specified, matching ensures the value fits in the space expected.
;; An Rvar refers to a pattern variable in scope.
;; NOTE: If the variable is mapped, an equality check will occur without checking
;;       if the value is in the specified Space (it is assumed to succeed).
;; NOTE: I say morally for immutable, since Racket doesn't have the best support for immutable vectors.
;;       We use standard vectors.
(struct Bvar (x Space-name) #:transparent)
(struct Rvar (x) #:transparent)
(define ρ₀ (hash))
(define ∅ (set))
(define (Avar x) (Bvar x #f))

;; A DPattern (or "data pattern") is either
;; - an atom
;; - a (Variant Name Immutable-Vector[DPattern]) (morally)

;; A binding is one of
;; - (Binding Pattern Expression)
;; - (Store-extend Expression Expression Boolean)
(struct Binding (lhs rexpr) #:transparent)
(struct Store-extend (key-expr val-expr trust-strong?) #:transparent)
;; OPT-OP: allow specialized Store-extend and Alloc forms that know statically 
;;         which address space they're using/producing addresses from/to
;; By treating store extensions as bindings, we can control the store flow.
;; We also don't need to make intermediate store names, which is a plus.

;; An Expression is one of
;; - (Term Pattern)
;; - Boolean
;; - (Map-lookup Symbol Expression Boolean Expression)
;; - (Map-extend Symbol Expression Expression Boolean)
;; - (Store-lookup Expression)
;; - (Alloc Any)
;; - (Meta-function-call name Pattern)
;; - (If Expression Expression Expression)
;; - (Let List[Binding] Expression
;; - (Equal Expression Expression)
;; - (In-Dom Symbol Expression)
;; - (Empty-set)
;; - (Set-Union List[Expression])
;; - (Set-Add* Expression List[Expression])
;; - (In-Set Expression Expression)

;; A Qualified-Expression (or QExpression) is an Expression,
;; except Alloc forms are QAlloc forms.

;; Notes: The boolean in Map-extend is whether the map should remain a strong update through abstraction.
;; This only matters for maps that have addresses in their domains.

(struct Term (pat) #:transparent)

(struct Map-lookup (mvar key-expr default? def-expr) #:transparent)
(struct Map-extend (mvar key-expr val-expr trust-strong?) #:transparent)
(struct Store-lookup (key-expr) #:transparent)
(struct Meta-function-call (name arg-pat) #:transparent)
(struct Alloc () #:transparent)
(struct QAlloc (hint) #:transparent)
(struct If (g t e) #:transparent)
(struct Equal (l r) #:transparent)
(struct Let (bindings body-expr) #:transparent)
(struct In-Dom (mvar key-expr) #:transparent)

(struct Set-Union (exprs) #:transparent)
(struct Empty-set () #:transparent)
(struct Set-Add* (set-expr exprs) #:transparent)
(struct In-Set (set-expr expr) #:transparent)

(struct Unsafe-store-space-ref () #:transparent)
(struct Unsafe-store-ref (space) #:transparent)

;; If expecting a set, make an arbitrary choice.
(struct Choose (expr) #:transparent)

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
;; (Meta-function Symbol List[Rule] Option[DPattern → DPattern] Option[DPattern → ℘(DPattern)])
;; TODO: termination back-door?
(struct Meta-function (name rules trusted-implementation/conc trusted-implementation/abs) #:transparent)

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

;; An Endpoint is an (Endpoint Variant-Address Space-Name)
(struct Endpoint (address space) #:transparent)
(struct Space-node (name trust) #:transparent)
