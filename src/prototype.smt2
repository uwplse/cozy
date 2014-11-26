; Translation of Haskell into SMT so Z3 can generate instances of Plan
(set-logic UF)

; Query specific
(declare-datatypes () ((QueryVar x y)))

(declare-datatypes () ((Field Age Name)))

(declare-datatypes () ((Comparison Eq Gt Ge Lt Le)))

(declare-datatypes () ((Query
    TrueQuery
    FalseQuery
    (Cmp (cmpField Field) (cmpOp Comparison) (cmpVar QueryVar))
    (And (andLeft Query) (andRight Query))
    (Or (orLeft Query) (orRight Query))
    (Not (notQ Query))
)))

(declare-datatypes () ((Plan
    All
    None
    (HashLookup (hashPlan Plan) (hashField Field) (hashVar QueryVar))
    (BinarySearch (bsPlan Plan) (bsField Field) (bsOp Comparison) (bsVar QueryVar))
    (Filter (filterPlan Plan) (filterQuery Query))
    (Intersect (isectFirstPlan Plan) (isectSecondPlan Plan))
    (Union (uFirstPlan Plan) (uSecondPlan Plan))
)))

; Can a plan produce a list sorted by the given field?
(define-fun isSortedBy ((p Plan) (f Field)) Bool
    (ite (is-All p) true
    (ite (is-None p) true
    (ite (is-BinarySearch p) (= (bsField p) f)
    (ite (is-HashLookup p) true
    false)))))

; A simple ordering on plans, used for breaking symmetry
(define-fun planLe ((p1 Plan) (p2 Plan)) Bool
    (and
    (=> (is-None p1)         (or (is-None p2) (is-HashLookup p2) (is-BinarySearch p2) (is-Filter p2) (is-Intersect p2) (is-Union p2)))
    (=> (is-HashLookup p1)   (or (is-HashLookup p2) (is-BinarySearch p2) (is-Filter p2) (is-Intersect p2) (is-Union p2)))
    (=> (is-BinarySearch p1) (or (is-BinarySearch p2) (is-Filter p2) (is-Intersect p2) (is-Union p2)))
    (=> (is-Filter p1)       (or (is-Filter p2) (is-Intersect p2) (is-Union p2)))
    (=> (is-Intersect p1)    (or (is-Intersect p2) (is-Union p2)))
    (=> (is-Union p1)        (is-Union p2))
    ))

; Simple projections
(define-fun leftPlan ((p Plan)) Plan
    (ite (is-HashLookup p)   (hashPlan p)
    (ite (is-BinarySearch p) (bsPlan p)
    (ite (is-Filter p)       (filterPlan p)
    (ite (is-Intersect p)    (isectFirstPlan p)
    (ite (is-Union p)        (uFirstPlan p)
    All))))))
(define-fun rightPlan ((p Plan)) Plan
    (ite (is-Intersect p)    (isectSecondPlan p)
    (ite (is-Union p)        (isectFirstPlan p)
    All)))
(define-fun leftQuery ((q Query)) Query
    (ite (is-And q) (andLeft q)
    (ite (is-Or q)  (orLeft q)
    (ite (is-Not q) (notQ q)
    TrueQuery))))
(define-fun rightQuery ((q Query)) Query
    (ite (is-And q) (andRight q)
    (ite (is-Or q)  (orRight q)
    TrueQuery)))

; Is the plan well-formed?
(define-fun isTrivialPlan ((p Plan)) Bool (or (= p All) (= p None)))
(define-fun planWf1 ((p Plan)) Bool (isTrivialPlan p))
(define-fun planWf2 ((p Plan)) Bool
    (and
    (planWf1 (leftPlan p))
    (planWf1 (rightPlan p))
    (=> (is-HashLookup p) (or (is-All (hashPlan p)) (is-HashLookup (hashPlan p))))
    (=> (is-BinarySearch p) (isSortedBy (bsPlan p) (bsField p)))
    (=> (is-Intersect p) (and
        (not (isTrivialPlan (isectFirstPlan p))) (not (isTrivialPlan (isectSecondPlan p)))
        (planLe (isectFirstPlan p) (isectSecondPlan p))))
    (=> (is-Union p) (and
        (not (isTrivialPlan (uFirstPlan p))) (not (isTrivialPlan (uSecondPlan p)))
        (planLe (uFirstPlan p) (uSecondPlan p))))
    ))
(define-fun planWf3 ((p Plan)) Bool
    (and
    (planWf2 (leftPlan p))
    (planWf2 (rightPlan p))
    (=> (is-HashLookup p) (or (is-All (hashPlan p)) (is-HashLookup (hashPlan p))))
    (=> (is-BinarySearch p) (isSortedBy (bsPlan p) (bsField p)))
    (=> (is-Intersect p) (and
        (not (isTrivialPlan (isectFirstPlan p))) (not (isTrivialPlan (isectSecondPlan p)))
        (planLe (isectFirstPlan p) (isectSecondPlan p))))
    (=> (is-Union p) (and
        (not (isTrivialPlan (uFirstPlan p))) (not (isTrivialPlan (uSecondPlan p)))
        (planLe (uFirstPlan p) (uSecondPlan p))))
    ))
(define-fun planWf4 ((p Plan)) Bool
    (and
    (planWf2 (leftPlan p))
    (planWf2 (rightPlan p))
    (=> (is-HashLookup p) (or (is-All (hashPlan p)) (is-HashLookup (hashPlan p))))
    (=> (is-BinarySearch p) (isSortedBy (bsPlan p) (bsField p)))
    (=> (is-Intersect p) (and
        (not (isTrivialPlan (isectFirstPlan p))) (not (isTrivialPlan (isectSecondPlan p)))
        (planLe (isectFirstPlan p) (isectSecondPlan p))))
    (=> (is-Union p) (and
        (not (isTrivialPlan (uFirstPlan p))) (not (isTrivialPlan (uSecondPlan p)))
        (planLe (uFirstPlan p) (uSecondPlan p))))
    ))
(define-fun planWf ((p Plan)) Bool (planWf4 p))

; The type of values in our system
; (TODO: Prove that this three-value system is equivalent to real arithmetic
; for our purposes.)
(declare-datatypes () ((Val lo mid hi)))

; Does a comparison hold?
(define-fun val-gt ((a Val) (b Val)) Bool
    (and
    (=> (= a hi)  (not (= b hi)))
    (=> (= a mid) (= b lo))
    (=> (= a lo)  false)
    ))
(define-fun cmpDenote ((cmp Comparison) (a Val) (b Val)) Bool
    (and
    (=> (= cmp Eq) (= a b))
    (=> (= cmp Gt) (val-gt a b))
    (=> (= cmp Ge) (or (= a b) (val-gt a b)))
    (=> (= cmp Lt) (not (or (= a b) (val-gt a b))))
    (=> (= cmp Le) (not (val-gt a b)))
    ))

; Select the right field value
(define-fun get-field ((f Field) (ageVal Val) (nameVal Val)) Val
    (ite (= f Age) ageVal nameVal))

; Select the right query var value
(define-fun get-queryvar ((qv QueryVar) (xVal Val) (yVal Val)) Val
    (ite (= qv x) xVal yVal))

; Does a query return true for a concrete (age, name) record?
(define-fun queryDenote1 ((q Query) (ageVal Val) (nameVal Val) (xVal Val) (yVal Val)) Bool
    (ite (is-TrueQuery q) true
    (ite (is-FalseQuery q) false
    (ite (is-Cmp q) (cmpDenote (cmpOp q) (get-field (cmpField q) ageVal nameVal) (get-queryvar (cmpVar q) xVal yVal))
    false))))
(define-fun queryDenote2 ((q Query) (ageVal Val) (nameVal Val) (xVal Val) (yVal Val)) Bool
    (let ((denote1 (queryDenote1 (leftQuery q) ageVal nameVal xVal yVal)) (denote2 (queryDenote1 (rightQuery q) ageVal nameVal xVal yVal)))
    (ite (is-TrueQuery q) true
    (ite (is-FalseQuery q) false
    (ite (is-Cmp q) (cmpDenote (cmpOp q) (get-field (cmpField q) ageVal nameVal) (get-queryvar (cmpVar q) xVal yVal))
    (ite (is-And q) (and denote1 denote2)
    (ite (is-Or q)  (or denote1 denote2)
    (ite (is-Not q) (not denote1)
    false))))))))
(define-fun queryDenote3 ((q Query) (ageVal Val) (nameVal Val) (xVal Val) (yVal Val)) Bool
    (let ((denote1 (queryDenote2 (leftQuery q) ageVal nameVal xVal yVal)) (denote2 (queryDenote2 (rightQuery q) ageVal nameVal xVal yVal)))
    (ite (is-TrueQuery q) true
    (ite (is-FalseQuery q) false
    (ite (is-Cmp q) (cmpDenote (cmpOp q) (get-field (cmpField q) ageVal nameVal) (get-queryvar (cmpVar q) xVal yVal))
    (ite (is-And q) (and denote1 denote2)
    (ite (is-Or q)  (or denote1 denote2)
    (ite (is-Not q) (not denote1)
    false))))))))
(define-fun queryDenote4 ((q Query) (ageVal Val) (nameVal Val) (xVal Val) (yVal Val)) Bool
    (let ((denote1 (queryDenote3 (leftQuery q) ageVal nameVal xVal yVal)) (denote2 (queryDenote3 (rightQuery q) ageVal nameVal xVal yVal)))
    (ite (is-TrueQuery q) true
    (ite (is-FalseQuery q) false
    (ite (is-Cmp q) (cmpDenote (cmpOp q) (get-field (cmpField q) ageVal nameVal) (get-queryvar (cmpVar q) xVal yVal))
    (ite (is-And q) (and denote1 denote2)
    (ite (is-Or q)  (or denote1 denote2)
    (ite (is-Not q) (not denote1)
    false))))))))
(define-fun queryDenote ((q Query) (ageVal Val) (nameVal Val) (xVal Val) (yVal Val)) Bool
    (queryDenote4 q ageVal nameVal xVal yVal))

; Does a plan include a concrete (age, name) record?
(define-fun planIncludes1 ((p Plan) (ageVal Val) (nameVal Val) (xVal Val) (yVal Val)) Bool
    (= p All))
(define-fun planIncludes2 ((p Plan) (ageVal Val) (nameVal Val) (xVal Val) (yVal Val)) Bool
    (let ((inc1 (planIncludes1 (leftPlan p) ageVal nameVal xVal yVal)) (inc2 (planIncludes1 (rightPlan p) ageVal nameVal xVal yVal)))
    (and
    (=> (is-None p) false)
    (=> (is-HashLookup p) (and inc1 (= (get-field (hashField p) ageVal nameVal) (get-queryvar (hashVar p) xVal yVal))))
    (=> (is-BinarySearch p) (and inc1 (cmpDenote (bsOp p) (get-field (bsField p) ageVal nameVal) (get-queryvar (bsVar p) xVal yVal))))
    (=> (is-Filter p) (and inc1 (queryDenote1 (filterQuery p) ageVal nameVal xVal yVal)))
    (=> (is-Intersect p) (and inc1 inc2))
    (=> (is-Union p) (or inc1 inc2))
    )))
(define-fun planIncludes3 ((p Plan) (ageVal Val) (nameVal Val) (xVal Val) (yVal Val)) Bool
    (let ((inc1 (planIncludes2 (leftPlan p) ageVal nameVal xVal yVal)) (inc2 (planIncludes2 (rightPlan p) ageVal nameVal xVal yVal)))
    (and
    (=> (is-None p) false)
    (=> (is-HashLookup p) (and inc1 (= (get-field (hashField p) ageVal nameVal) (get-queryvar (hashVar p) xVal yVal))))
    (=> (is-BinarySearch p) (and inc1 (cmpDenote (bsOp p) (get-field (bsField p) ageVal nameVal) (get-queryvar (bsVar p) xVal yVal))))
    (=> (is-Filter p) (and inc1 (queryDenote2 (filterQuery p) ageVal nameVal xVal yVal)))
    (=> (is-Intersect p) (and inc1 inc2))
    (=> (is-Union p) (or inc1 inc2))
    )))
(define-fun planIncludes4 ((p Plan) (ageVal Val) (nameVal Val) (xVal Val) (yVal Val)) Bool
    (let ((inc1 (planIncludes3 (leftPlan p) ageVal nameVal xVal yVal)) (inc2 (planIncludes3 (rightPlan p) ageVal nameVal xVal yVal)))
    (and
    (=> (is-None p) false)
    (=> (is-HashLookup p) (and inc1 (= (get-field (hashField p) ageVal nameVal) (get-queryvar (hashVar p) xVal yVal))))
    (=> (is-BinarySearch p) (and inc1 (cmpDenote (bsOp p) (get-field (bsField p) ageVal nameVal) (get-queryvar (bsVar p) xVal yVal))))
    (=> (is-Filter p) (and inc1 (queryDenote3 (filterQuery p) ageVal nameVal xVal yVal)))
    (=> (is-Intersect p) (and inc1 inc2))
    (=> (is-Union p) (or inc1 inc2))
    )))
(define-fun planIncludes ((p Plan) (ageVal Val) (nameVal Val) (xVal Val) (yVal Val)) Bool
    (planIncludes4 p ageVal nameVal xVal yVal))

; Does a plan actually implement a query?
(define-fun implements ((p Plan) (q Query)) Bool
    (forall ((ageVal Val) (nameVal Val) (xVal Val) (yVal Val))
        (= (planIncludes p ageVal nameVal xVal yVal) (queryDenote q ageVal nameVal xVal yVal))))

; Query to synthesize for
; (define-const query Query (And (Cmp Age Gt x) (Cmp Name Eq y)))
; (define-const query Query (Cmp Age Eq x))
; (define-const query Query (Or (Cmp Age Eq x) (Cmp Age Lt x)))
(define-const query Query (Or (Cmp Age Eq x)
       (And (Cmp Age Gt y)
            (Cmp Age Lt x))))

; Actual output being synthesized
(declare-const plan Plan)
(assert (planWf plan))
(assert (implements plan query))

(check-sat)
(get-model)
