; Translation of Haskell into SMT so Z3 can generate instances of Plan

; Query specific
(declare-datatypes () ((QueryVar x y)))
(declare-datatypes () ((Field Age Name)))

(declare-datatypes () ((Comparison Eq Gt)))
(declare-datatypes () ((Query
    TrueQuery
    FalseQuery
    (Cmp (cmpField Field) (cmpOp Comparison) (cmpVar QueryVar))
    (And (left Query) (right Query))
)))
;(declare-sort Query 0)
;(declare-fun queryContains (Query Query) bool)
;(assert (forall ((q Query) (r Query))
    ;(or (not (= q r)) (queryContains q r))
;))
;(assert (forall ((q Query) (r Query))
    ;(or (not (is-And r)) (and (queryContains q (left r)) (queryContains q (right r))))
;))
;(assert (forall ((q Query) (r Query))
    ;(iff
        ;(queryContains q r)
        ;(or
            ;(= q r)
            ;(and (is-And r) (or (queryContains q (left r)) (queryContains q (right r))))
;))))
; Needle and Haystack
(define-fun queryContainsBot ((n Query) (h Query)) bool
    (= n h)
)
(define-fun queryContains1 ((n Query) (h Query)) bool
    (or
        (= n h)
        (and (is-And h) (or (queryContainsBot n (left h)) (queryContainsBot n (right h))))
))
(define-fun queryContains ((n Query) (h Query)) bool
    (or
        (= n h)
        (and (is-And h) (or (queryContains1 n (left h)) (queryContains1 n (right h))))
))

; check if a --> q (actually want a <--> q?)
(define-fun impliesBot ((a Query) (q Query)) bool
    (queryContains q a)
)
(define-fun implies1 ((a Query) (q Query)) bool
    (or
        (queryContains q a)
        (and (is-And q) (and (impliesBot a (left q)) (impliesBot a (right q))))
))
(define-fun impliesQuery ((a Query) (q Query)) bool
    (or
        (queryContains q a)
        (and (is-And q) (and (implies1 a (left q)) (implies1 a (right q))))
))

;(define-fun And ((q Query) (r Query)))

(declare-datatypes () ((Plan
    All
    None
    (HashLookup (hashField Field) (hashVar QueryVar))
    (BinarySearch (bsField Field) (bsOp Comparison) (bsVar QueryVar))
    (Filter (filterPlan Plan) (filterQuery Query))
    (SubPlan (outerPlan Plan) (innerPlan Plan))
    (Intersect (isectFirstPlan Plan) (isectSecondPlan Plan))
)))

; Query specific
; Query (define-fun defines constants; declare-const defines variables)
(define-fun query () Query (And (Cmp Age Gt x) (Cmp Name Eq y)))

; Actual output being synthesized
(declare-const plan Plan)

(define-fun postCondBot ((p Plan)) Query
    (ite (is-All p) TrueQuery
    (ite (is-None p) FalseQuery
    (ite (is-HashLookup p) (Cmp (hashField p) Eq (hashVar p))
    (ite (is-BinarySearch p) (Cmp (bsField p) (bsOp p) (bsVar p))
        FalseQuery
    ))))
)
(define-fun postCond1 ((p Plan)) Query
    (ite (is-All p) TrueQuery
    (ite (is-None p) FalseQuery
    (ite (is-HashLookup p) (Cmp (hashField p) Eq (hashVar p))
    (ite (is-BinarySearch p) (Cmp (bsField p) (bsOp p) (bsVar p))
    (ite (is-Filter p) (And (postCondBot (filterPlan p)) (filterQuery p))
    (ite (is-SubPlan p) (And (postCondBot (outerPlan p)) (postCondBot (innerPlan p)))
    (ite (is-Intersect p) (And (postCondBot (isectFirstPlan p)) (postCondBot (isectSecondPlan p)))
        FalseQuery
    )))))))
)
(define-fun postCond ((p Plan)) Query
    (ite (is-All p) TrueQuery
    (ite (is-None p) FalseQuery
    (ite (is-HashLookup p) (Cmp (hashField p) Eq (hashVar p))
    (ite (is-BinarySearch p) (Cmp (bsField p) (bsOp p) (bsVar p))
    (ite (is-Filter p) (And (postCond1 (filterPlan p)) (filterQuery p))
    (ite (is-SubPlan p) (And (postCond1 (outerPlan p)) (postCond1 (innerPlan p)))
    (ite (is-Intersect p) (And (postCond1 (isectFirstPlan p)) (postCond1 (isectSecondPlan p)))
        FalseQuery
    )))))))
)

;(define-fun implies ((q Query) (r Query)) bool
    ;(ite (
    ;)
;)

; Query equivalent of plan
(define-fun pq () Query (postCond plan))

(assert (impliesQuery pq query))
(assert (impliesQuery query pq))

(check-sat)
(get-model)
