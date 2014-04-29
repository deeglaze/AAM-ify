AAM-ify
=======

A PLT Redex-inspired language of operational semantics with an automatic "abstracting abstract machines" transformation.

Auditing the code
-----
The code is heavily commented with design decisions, descriptions of abstractions and rationale.
The following tags have significance:

**TODO[?]:**
  A point in the code where an addition is necessary/suggested (respectively) for later commits.

**FIXME[?]:**
  A piece of code that is absolutely broken or needs re-evaluation later (respectively).

**XXX:**
  Discusses caveats to a design decision, or a less sure "FIXME?"

**INVARIANT:**
  Description of a property that should hold invariably.

**ASSUMPTION:**
  Like an invariant, but based more on user interaction than program behavior.

**UNCHECKED ASSUMPTION:**
  An unproven/poorly justified proposition about user interaction.

**OPT:**
  Description of how some piece of code/data structure was optimized.

**OPT-OP:**
  An unimplemented idea for an optimization opportunity.

**NOTE:**
  A decidedly tricky piece of code follows. This note is a careful explanation.

ADDITIONAL FEATURES:
-----
* abstract counting for better equality matching
* "address spaces" divvy items amongst as many stores that get automatically added.
* Addresses can be marked for pointer equality, or for equality to automatically dereference.
    * Addresses introduced by the AAM transformation are the latter kind, in the 'AAM address space.
* finite functions (dictionaries) and sets are natively supported. The burden of ensuring associativity/commutivity of meta-functions on these data is left to the user.

PLANNED WISHLIST:
-----
* build an escape hatch for smarter lattices.
* widening for control flow
* automatic garbage collection in (to add) "weak maps" across address spaces.
  Addresses of different spaces can occur in mapped objects.
* pattern support for sets and maps (currently we use side-conditions)
* add a new "binding" form like When, only non-local. Failure leads to trying the next major rule.
* Synthesize a better alloc skeleton with more user guidance/annotations.
* Drop distinction between terms and expressions. Variant constructors and meta-functions inhabit same namespace.

UNPLANNED WISHLIST:
------
* a compiler to output specialized Racket code implementing an input language's semantics.
* a higher-level language with binding specifications, synthesized substitution and
  contextual matching that compiles to a closure-based semantics and reified continuations.


SHOW-STOPPING FIXMEs:
-----
* We need to track positions where maps and sets flow, and what the expected spaces are,
  so we can mark them as abstract (with pointer to cardinality analysis) or not when
  constructing them.
