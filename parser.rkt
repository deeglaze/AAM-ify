#lang racket/base

#|
Language forms require extra annotations for performance reasons.
These annotations are easy for a program to perform, but annoying for humans.

This module defines a syntactic front-end to defining languages,
their semantics and associated meta-functions.

A plus to using syntax is that errors can use syntax-location.

Languages are special since they introduce several names that will be
used by rules, expressions, patterns and meta-functions. As such,
not only will parsed languages produce the expected Language value with
maps of symbols to spaces, but also a syntax-time value for associating
identifiers for syntax errors.

TODO?: Add binding arrows using DrRacket's API
|#
(require "spaces.rkt"
         racket/match
         syntax/parse racket/syntax syntax/id-table)
(provide parse-expression
         parse-language
         parse-rule)

(define-literal-set expr-ids
  (Term
   Map-lookup
   Map-extend
   Store-lookup
   If
   Let
   Equal
   In-Dom
   Empty-set
   Set-Union
   Set-Add*
   In-Set
   Meta-function-call
   Store-extend
   SAlloc
   MAlloc
   QSAlloc
   QMAlloc))

(define-literal-set pat-ids
  (Bvar
   Rvar
   variant))

(struct with-orig-stx (v stx) #:transparent)

(define (flatten-space space)
  (define s (match space [(with-orig-stx s* _) s*] [other other]))
  (match s
    [(User-Space variants trust-recursion?)
     (User-Space (for/list ([v (in-list variants)])
                   (if (Variant? v)
                       (flatten-variant v)
                       (flatten-component v)))
                 trust-recursion?)]
    ;; FIXME: How do users type these in as syntax?
    [(External-Space pred cardinality precision special-equality)
     s]
    [(Address-Space space)
     (Address-Space (syntax-e space))]
))
;; Parsed values are comprised of syntax objects.
(define (flatten-pattern pat)
  (define pat*
    (match pat [(with-orig-stx pat* _) pat*] [other other]))
  (match pat*
    [(Bvar id (with-orig-stx space _))
     (Bvar (syntax-e id (flatten-space space)))]
    [(Rvar id) (Rvar (syntax-e id))]
    [(variant (with-orig-stx var _) pats)
     (variant (flatten-Variant var)
              (for/vector #:length (vector-length pats)
                          ([p (in-vector pats)])
                          (flatten-pattern p)))]
    [(abstract-ffun map) ...]
    [(discrete-ffun map) ...]
    [(? dict? map) ...]
    [(? set? pats) ...]
    [(Address-Structural space addr) ...]
    [(Address-Egal space addr) ...]))

(define (flatten-Variant v)
  (define var (match v [(with-orig-stx v* _) v*] [other other]))
  (match var
    [(Variant name comps)
     (Variant (syntax-e name)
              (for/vector #:length (vector-length comps)
                          ([comp (in-vector comps)])
                (flatten-Component comp)))]))

(define (flatten-Component c)
  (define comp (match c [(with-orig-stx c* _) c*] [other other]))
  (match comp
    [(Space-reference name) (Space-reference (syntax-e name))]
    [(Map dom rng) (Map (flatten-component dom) (flatten-Component rng))]
    [(℘ comp) (flatten-Component comp)]
    [(? Anything?) comp]))

(define/match (flatten-language L)
  [(Language name spaces)
   (Language (syntax-e name)
             (let loop ([itr (free-id-table-iterate-first spaces)]
                        [h #hash()])
               (if itr
                   (loop (free-id-table-iterate-next spaces itr)
                         (hash-set h
                                   (syntax-e (free-id-table-iterate-key spaces itr))
                                   (flatten-space (free-id-table-iterate-value spaces itr))))
                   h)))])

(define-syntax-class (Space-ref L)
  #:attributes (space)
  [s:id #:do [(define spaces (Language-spaces L))]
        #:fail-unless (free-id-table-has-key? spaces #'s)
        (format "Unknown space name ~a" (syntax-e #'s))
        #:attr space (free-id-table-ref spaces #'s)])

(define (find-suitable-variant L expected-space vname pats)
  (define fpats (delay (vector-map (λ (vc)
                                      (if (variant? vc)
                                          (flatten-variant vc)
                                          (flatten-component vc)))
                                   pats)))
  (define fL (delay (flatten-language L)))
  (define (check-space s v)
    (match-define (User-Space v-or-cs _) s)
    (for/or ([v-or-c (in-list v-or-cs)]
             #:when (and (Variant? v-or-c)
                         (free-id-equal?
                          (Variant-name v-or-c)
                          vname)))
      (in-variant? (force fL)
                   (flatten-variant v-or-c)
                   fv)
      (and
       (if (Variant? v-or-c)
           
           (in-component? (force fL) (flatten-component v-or-c) fv))
       v-or-c)))
  (if expected-space
      (check-space expected-space v)
      (for/or ([s (in-free-id-table-values (Language-spaces L))]
               #:when (User-Space? s))
        (check-space s v))))

(define-syntax-class (Variant-ref L expected-space)
  #:attributes (variant)
  [v:id #:do [(define spaces (Language-spaces L))]
        #:fail-unless (free-id-table-has-key? spaces #'s)
        (format "Unknown space name ~a" (syntax-e #'s))
        #:attr space (free-id-table-ref spaces #'s)])

(define-syntax-class (Pattern L)
  #:literal-set (pat-ids)
  #:attributes (pat)
  [(Bvar v:id (~optional (~var S (Space-ref L))))
   #:attr pat (Bvar v (attribute S.space))]
  [(Rvar v:id) #:attr pat (Rvar #'v)]
  [((~var variant (Variant-ref L)) (~var ps (Pattern L)) ...)])

(define (parse-expression L stx)
  (syntax-parse stx
    [(Term pat)]))