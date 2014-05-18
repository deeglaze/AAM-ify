#lang racket/base

#|
Utility functions and specific functions that are shared between concrete and abstract AAM
|#

(require racket/match racket/set racket/dict "spaces.rkt"
         racket/unit
         (only-in math/number-theory binomial)
         racket/trace
         (for-syntax racket/base syntax/parse (only-in "spaces.rkt" debug-mode)))
(provide unbound-map-error
         pattern-eval
         apply-reduction-relation
         apply-reduction-relation*
         apply-reduction-relation*/memo
         store-ref store-set store-op
         in-space? in-component?
         hash-join
         hash-add
         for/union
         for*/union
         set-add*
         sexp-to-dpattern/check
         dpattern->sexp
         log-thread)

(define-for-syntax (drop stx) #'(void))
(define-syntax (make-debug-rename stx)
  (syntax-parse stx
    [(_ name:id x:id)
     #`(begin
         #,(if debug-mode
               #'(define-syntax name (make-rename-transformer #'x))
               #'(define-syntax name drop))
         (provide name))]))
(make-debug-rename dwhen when)
(make-debug-rename dprintf printf)
(make-debug-rename dtrace trace)

(define (unbound-map-error who m) (λ () (error who "Map unbound ~a" m)))

;; pattern-eval : Pattern Map[Symbol,DPattern] → DPattern
;; Concretize a pattern given an environment of bindings.
(define (pattern-eval pat ρ)
  (match pat
    [(Rvar x) (hash-ref ρ x (λ () (error 'pattern-eval "Unbound pattern variable ~a" x)))]
    [(variant var pats) (variant var (for/vector #:length (vector-length pats)
                                                 ([pat (in-vector pats)])
                                          (pattern-eval pat ρ)))]
    [(or (? Datum?) (? boolean?)) pat]
    [(or (? Name?) (? is-a?) (? Map-with?) (? Set-with?))
     (error 'pattern-eval "Cannot eval a binding pattern ~a" pat)]
    [atom atom]))

(define (apply-reduction-relation rule-eval R)
  (define rules (Reduction-Relation-rules R))
  (λ (term)
   (for/union ([rule (in-list rules)]) (rule-eval rule term))))

(define (extend-indefinitely F x)
  (match (F x)
    [(? set-empty?) (set x)]
    [outs (for/union ([term* (in-set outs)]) (extend-indefinitely F term*))]))

(define (apply-reduction-relation* rule-eval R)
  (define reduce (apply-reduction-relation rule-eval R))
  (λ (term) (extend-indefinitely reduce term)))

(define (apply-reduction-relation*/memo rule-eval R)
  (define reduce (apply-reduction-relation rule-eval R))
  (λ (term)
     (define seen (mutable-set))
     (let fix ([term term])
       (cond
        [(set-member? seen term) ∅]
        [else
         (set-add! seen term)
         (match (reduce term)
           [(? set-empty?) (set term)]
           [outs (for/union ([term* (in-set outs)]) (fix term*))])]))))

;; in-space? : DPattern Language Space-name → Boolean
;; Decide whether a DPattern d is in Space space-name, which is defined in Language L.
(define (in-space-ref? L space-name d)
  (cond
   [(eq? space-name 'Bool)
    (boolean? d)]
   [else
    (define spaces (Language-spaces L))
    (define space
      (hash-ref spaces space-name
                (λ () (error 'in-space? "Undefined space ~a"
                             space-name))))
    (in-space? L space d)]))

(define (in-space? L space d)
  (define spaces (Language-spaces L))
  (match space
    [(User-Space c _ _) (in-component? L c d)]
    ;; XXX: should external space predicates be allowed to return 'b.⊤?
    [(? External-Space?)
     (define pred (External-Space-pred space))
     (match d
       [(external (== space) _) #t]
       [v (pred v)])]
    [_ (error 'in-space? "Bad space ~a" space)]))

(define (in-component? L comp d)
  (match comp
    [(∪ _ comps)
     (for/or ([c (in-list comps)]) (in-component? L c d))]
    [(Variant _ name comps _ _)
     (match d
       [(variant (Variant _ (== name) _ _ _) ds)
        (for/and ([comp (in-vector comps)]
                  [d (in-vector ds)])
          (in-component? L comp d))]
       [_ #f])]
    [(? Space-reference?)
     (in-space-ref? L (Space-reference-name comp) d)]
    [(Map _ _ domain range)
     (define (check-map d)
       (for/and ([(k v) (in-dict d)])
         (and (in-component? L domain k)
              (in-component? L range v))))
     (match d
       [(ffun _ m) (check-map m)]
       [_ #f])]
    [(℘ _ _ comp)
     (match d
       [(fset _ S)
        (for/and ([v (in-set S)]) (in-component? L comp v))]
       [_ #f])]
    [(Address-Space space match-behavior equal-behavior)
     (match d
       [(Address (== space eq?) _ (== match-behavior eq?) (== equal-behavior eq?)) #t]
       [_ #f])]
    [(? Bool?) (boolean? d)]
    [(or (? Datum? d*) (? boolean? d*)) (equal? d d*)]
    [_ (error 'in-component? "Bad component ~a" comp)]))
(dtrace in-component?)

;; sexp-to-dpattern/check : S-exp Space-name Language → DPattern
;; A minor parser from sexp to internal representation.
;; Any head-position constructor is considered a variant.
;; Ensure all variants exist in L.
(define (sexp-to-dpattern/check sexp expected-space-name L)
  (define spaces (Language-spaces L))
  (define (component-sexp-to-dpat comp sexp)
    (match comp
      [(℘ _ _ comp)
       (unless (set? sexp)
         (error 'component-sexp-to-dpat "Expected a set of ~a given ~a" comp sexp))
       (for/set ([s (in-set sexp)])
         (component-sexp-to-dpat comp s))]
      [(Map _ _ domain range)
       (unless (dict? sexp)
         (error 'component-sexp-to-dpat "Expected a map from ~a to ~a given ~a" domain range sexp))
       (for/hash ([(k v) (in-dict sexp)])
         (values (component-sexp-to-dpat domain k)
                 (component-sexp-to-dpat range v)))]
      [(? Space-reference?) (space-to-dpat (Space-reference-name comp) sexp)]
      [(or (? ∪?) (? Variant?)) (error 'sexp-to-dpattern/check "Bitrot")]
      [_ (error 'component-sexp-to-dpat "Bad component ~a" comp)]))

  (define (space-to-dpat space-name sexp)
    (define space
      (dict-ref spaces space-name
                (λ () (error 'sexp-to-dpattern/check
                             "Expected space undefined ~a" space-name))))
    (match space
      [(Address-Space space emb eeb)
       (Address space sexp
                (or emb core-match-default)
                (or eeb core-equal-default))] ;; An address may take any form.
      [(? External-Space?) (and ((External-Space-pred space) sexp) sexp)]
      [(User-Space c _ _) (component-sexp-to-dpat c sexp)]
      [_ (error 'space-to-dpat "Bad space ~a" space)]))
  (space-to-dpat expected-space-name sexp))

(define (dpattern->sexp d)
  (match d
    [(variant (Variant _ name _ _ _) ds)
     (cons name (for/list ([d (in-vector ds)]) (dpattern->sexp d)))]
    [(ffun _ d)
     (cons 'make-hash
           (for/list ([(k v) (in-dict d)])
             (list (dpattern->sexp k) (dpattern->sexp v))))]
    [(external _ v) v]
    [(Datum atom) atom]))

;; Utility functions
(define (set-add* s args)
  (for/fold ([s s]) ([arg (in-list args)]) (set-add s arg)))

(define-syntax-rule (for/union guard body ...)
  (for/fold ([acc ∅]) guard (set-union acc (let () body ...))))
(define-syntax-rule (for*/union guard body ...)
  (for*/fold ([acc ∅]) guard (set-union acc (let () body ...))))

(define (hash-join h k v) (hash-set h k (set-union (hash-ref h k ∅) v)))
(define (hash-add h k v) (hash-set h k (set-add (hash-ref h k ∅) v)))


(define (store-ref store-spaces k)
  (match k
    [(Address space addr _ _)
     (hash-ref (hash-ref store-spaces space #hash())
               addr
               (λ () (error 'store-ref "Unmapped address ~a" k)))]
    [_ (error 'store-ref "Bad address ~a" k)]))

(define (store-op who op)
  (λ (store-spaces k v)
     (match k
       [(Address space addr _ _)
        (hash-set store-spaces
                  space
                  (op (hash-ref store-spaces space #hash()) addr v))]
       [_ (error who "Bad address ~a" k)])))
(define store-set (store-op 'store-set hash-set))

(define-syntax log-thread
  (syntax-parser
    [(_ kind (~optional (~seq #:file path:expr (~bind [port (λ (p body)
                                                               #`(call-with-output-file*
                                                                  path
                                                                  (λ (#,p) #,body)
                                                                  #:exists 'replace))]))
                        #:defaults ([port (λ (p body) #`(let ([#,p (current-output-port)]) #,body))])))
     #`(let ([lr (make-log-receiver (current-logger) kind)])
         (thread (λ ()
                    #,((attribute port)
                       #'p
                       #'(let loop () (define vs (sync lr)) (write vs p) (newline p) (newline p) (loop))))))]))
