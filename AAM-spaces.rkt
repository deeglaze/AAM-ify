#lang racket/base

(require racket/set)
(provide (all-defined-out))
#|
Allow spaces to be inductively defined or provided with the promise that they are finite
Allow powerset constructor
Allow functions
Allow stores (special)

|#

;; A Language is a (Language name Map[Space-name,Either[Space,Component]])
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
;; - an (Address-Space)
;; - a (Map Component Component)
;; - a (℘ Component)
;; TODO?: Add a WeakMap option for automatic GC.

(struct Space-reference (name) #:transparent)
(struct Map (domain range) #:transparent)
(struct ℘ (component) #:transparent)

;; TODO?: allow variants or components to have side-conditions
(struct Variant (name Components) #:transparent)
(struct Address (addr) #:transparent)

;; A Card is one of
;; - 0
;; - 1
;; - 'ω


;; A Space is one of
;; - (User-Space List[Either[Variant,Component]] Boolean)
;; - (External-Space (Any → Boolean) (Any [Addr ↦ Card] → Card) Boolean)
;; - (Address-Space)
;; An external space has a predicate that decides membership,
;; a cardinality analysis for values of the space (may be given the abstract count [1] map), and
;; a boolean that is #t iff the cardinality analysis is ever note 1.
;;
;; A user space may not have duplicate variants.
(struct User-Space (variants trust-recursion?) #:transparent)
(struct Address-Space () #:transparent)
(struct External-Space (pred cardinality imprecise?) #:transparent)

;; A store is a map from Address-Space to (Space-ref Name).
;; The 'State space must have a store in each variant.

;; A reduction semantics is a List[Rule]
;; A rule is a (Rule Any Pattern Pattern List[Either[Binding,Side-condition]])
;; A Rule name is used for guiding allocation.

(struct Rule (name lhs rhs binding-side-conditions) #:transparent)

;; A Pattern is one of
;; - a (Bvar Symbol Option[Space-name])
;; - an (Rvar Symbol)
;; - a (Variant Name List[Pattern])
;; - an atom
;; Bvar patterns bind on the left if not already mapped.
;; If mapped, an equality check occurs before matching continues.
;; If a Space name is specified, matching ensures the value fits in the space expected.
;; An Rvar refers to a pattern variable in scope.
;; NOTE: If the variable is mapped, an equality check will occur without checking
;;       if the value is in the specified Space (it is assumed to succeed).
(struct Bvar (x Space-name) #:transparent)
(struct Rvar (x) #:transparent)
(define ρ₀ (hash))
(define ∅ (set))

;; A DPattern (or "data pattern") is either
;; - an atom
;; - a (Variant Name List[DPattern])

;; A binding is one of
;; - (PBinding Pattern Pattern)
;; - (EBinding Pattern Expression)
;; A PBinding is a shortcut for (EBinding pat (Term pat))
(struct PBinding (lhs rpat) #:transparent)
(struct EBinding (lhs rexpr) #:transparent)

;; An Expression is one of
;; - (Map-lookup Symbol Pattern Boolean Pattern)
;; - (Map-extend Symbol Pattern Pattern Boolean)
;; - (Map-lookup* Symbol Expression Boolean Expression)
;; - (Map-extend* Symbol Expression Expression Boolean)
;; - (Alloc Any)
;; - (Meta-function-call name Pattern)
;; - (If Expression Expression Expression)
;; - (Let List[Binding] Expression
;; - Boolean
;; - (Equal Expression Expression)
;; - (Empty-set)
;; - (Set-Union List[Expression])
;; - (Set-Add* Expression List[Expression])
;; - (In-Set Expression Expression)
;; - (Term Pattern)
(define (expression? e)
  (or (Map-lookup? e) (Map-lookup*? e) (Map-extend? e) (Map-extend*? e)
      (Alloc? e) (Meta-function-call? e)
      (If? e) (boolean? e) (Equal? e) (Term? e)))
;; Notes: The boolean in Map-extend is whether the map should remain a strong update through abstraction.
;; This only matters for maps that have addresses in their domains.

(struct Map-lookup (mvar key-pat default? dpat) #:transparent)
(struct Map-extend (mvar key-pat val-pat trust-strong?) #:transparent)
(struct Map-lookup* (mvar key-pat default? dpat) #:transparent)
(struct Map-extend* (mvar key-pat val-pat trust-strong?) #:transparent)
(struct Meta-function-call (name arg-pat) #:transparent)
(struct Alloc (hint) #:transparent)
(struct If (g t e) #:transparent)
(struct Equal (l r) #:transparent)
(struct Let (bindings body-expr) #:transparent)

(struct Term (pat) #:transparent)

(struct Set-union (exprs) #:transparent)
(struct Empty-set () #:transparent)
(struct Set-Add* (set-expr exprs) #:transparent)
(struct Set-In (set-expr expr) #:transparent)

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
