#!/usr/bin/env runhaskell

-- Meaningful names for different things
type Type = String
type Field = String
type QueryVar = String

-- Comparison operators
data Comparison = Eq | Gt
    deriving (Eq, Show)

-- Query language
-- A query is sort of like a predicate that operates over
-- one record with Fields and one set of QueryVars.
data Query =
    T | -- match everything
    F | -- match nothing
    Cmp Field Comparison QueryVar |
    And Query Query
    -- someday maybe we'll support "Or" as well
    deriving (Eq, Show)

-- Execution planning language
-- A plan is a program that returns a collection of elements. "What kind of
-- collection" is determined by the plan itself.
data Plan =
    All |
    None |
    HashLookup Plan Field QueryVar | -- get a collection by hash lookup
    BinarySearch Plan Field Comparison QueryVar | -- get a sorted list of elements
    Filter Plan Query | -- execute the plan, then filter the result according to the predicate
    Intersect Plan Plan | -- execute the left plan and right plan, keeping only elements from both result sets
    Union Plan Plan -- execute the left plan and right plan, keeping all elements from either result set
    deriving (Show)

-- Data structures
data DataStructure =
    Ty | -- the type over which the query computes, e.g. "Record"
    Empty | -- an empty collection
    HashMap Field DataStructure |
    SortedList Field DataStructure |
    UnsortedList DataStructure |
    Pair DataStructure DataStructure
    deriving (Show)

-- Cost model
data Cost =
    N | -- total number of elements in the structure
    Factor Rational |
    Log Cost |
    Times Cost Cost |
    Plus Cost Cost |
    Min Cost Cost
    deriving (Show)

isSortedBy :: Plan -> Field -> Bool
isSortedBy All _ = True
isSortedBy None _ = True
isSortedBy (BinarySearch _ f1 _ _) f2 = f1 == f2
isSortedBy (HashLookup _ _ _) _ = True
isSortedBy (Filter p _) f = isSortedBy p f
isSortedBy (Intersect p1 p2) f = p1 `isSortedBy` f && p2 `isSortedBy` f
isSortedBy (Union p1 p2) f = p1 `isSortedBy` f && p2 `isSortedBy` f

planWf :: Plan -> Bool
planWf All = True
planWf None = True
planWf (HashLookup All _ _) = True
planWf (HashLookup p@(HashLookup _ _ _) _ _) = planWf p
planWf (BinarySearch p f _ _) = planWf p && p `isSortedBy` f
planWf (Filter p _) = planWf p
planWf (Intersect p1 p2) = planWf p1 && planWf p2
planWf (Union p1 p2) = planWf p1 && planWf p2
planWf _ = False

-- For a given plan, extract the data structure necessary to execute it.
structureFor :: Plan -> DataStructure
structureFor p = helper p Ty
    where
        -- There is an asymmetry in the DataStructure type. "Ty"
        -- represents "one record" while the others represent
        -- "a collection of records". This function converts any
        -- DataStructure to a collection.
        mkPoly Ty = UnsortedList Ty
        mkPoly x = x

        helper All                      base = mkPoly base
        helper None                     base = Empty
        helper (HashLookup p f _)       base = helper p (HashMap f (mkPoly base))
        helper (BinarySearch p@(BinarySearch _ _ _ _) _ _ _) base = helper p base
        helper (BinarySearch p f cmp _) base = helper p (SortedList f base)
        helper (Filter p _)             base = helper p base
        helper (Intersect p1 p2)        base = Pair (helper p1 base) (helper p2 base)
        helper (Union p1 p2)            base = Pair (helper p1 base) (helper p2 base)

-- Estimate how long a plan takes to execute.
-- Our overall goal is to find a plan that minimizes this for large N.
cost :: Plan -> Cost
cost p = fst $ helper p N
    where
        -- helper returns (time, count)
        -- where count is the number of elements, and time is how long it
        -- took to find them
        helper All base = (Factor 1, base)
        helper None base = (Factor 1, Factor 0)
        -- The 0.5 below needs some justification...
        -- Basically, in the absence of any other info, we assume that the
        -- probability of an object matching a given predicate is 50%, so
        -- the subplan will execute on (we expect) half the data.
        helper (HashLookup p _ _) base =
            let (time, base') = helper p base
            in (Plus (Factor 1) time, Times base' (Factor 0.5))
        helper (BinarySearch p _ _ _) base =
            let (time, base') = helper p base
            in (Plus time (Log base'), Times base' (Factor 0.5))
        helper (Filter p _) base =
            let (time, base') = helper p base
            in (Plus time base', Times base' (Factor 0.5))
        helper (Intersect p1 p2) base =
            let (time1, base1) = helper p1 base
                (time2, base2) = helper p2 base
            in (Plus (Plus time1 time2) (Plus base1 base2),
                Times (Min base1 base2) (Factor 0.5))
        helper (Union p1 p2) base =
            let (time1, base1) = helper p1 base
                (time2, base2) = helper p2 base
            in (Plus (Plus time1 time2) (Plus base1 base2),
                Plus base1 base2)

-- for some value of N, figure out the concrete cost
evalCost :: Cost -> Double -> Double
evalCost N n = n
evalCost (Factor x) _ = fromRational x
evalCost (Log c) n = log (evalCost c n)
evalCost (Plus c1 c2) n = evalCost c1 n + evalCost c2 n
evalCost (Times c1 c2) n = evalCost c1 n * evalCost c2 n
evalCost (Min c1 c2) n = min (evalCost c1 n) (evalCost c2 n)

-- A query. Sort of like "SELECT * WHERE age > x AND name = y" where x and y can vary.
query = And (Cmp "age" Gt "x") (Cmp "name" Eq "y")

-- Various candidate plans to implement said query.
plan1 = Intersect (BinarySearch All "age" Gt "x") (HashLookup All "name" "y")
plan2 = BinarySearch (HashLookup All "name" "y") "age" Gt "x"
plan3 = Filter All query

main :: IO ()
main = do
    putStrLn $ "Query: " ++ show query
    mapM_ printPlanInfo [plan1, plan2, plan3]
    where
        printPlanInfo p = do
            print p
            putStrLn $ "    -->   structure = " ++ show (structureFor p)
            putStrLn $ "    -->   cost = " ++ show (evalCost (cost p) 100000)
