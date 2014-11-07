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
    T |  -- match everything
    F | -- match nothing
    Cmp Field Comparison QueryVar |
    And Query Query
    -- someday maybe we'll support Or too
    deriving (Eq, Show)

-- Execution planning language
data Plan =
    All |
    None |
    HashLookup Field QueryVar |
    BinarySearch Field Comparison QueryVar |
    Filter Plan Query |
    SubPlan Plan Plan |
    Intersect Plan Plan
    deriving (Show)

-- Data structures
data DataStructure =
    Ty | -- the type over which the query computes, e.g. "Record"
    HashMap Field DataStructure |
    SortedList Field DataStructure |
    UnsortedList DataStructure |
    Pair DataStructure DataStructure
    deriving (Show)

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

        helper All                    base = base
        helper (HashLookup f v)       base = HashMap f (mkPoly base)
        helper (BinarySearch f cmp v) base = SortedList f base
        helper (Filter p _)           base = helper p base
        helper (SubPlan p1 p2)        base = helper p1 (helper p2 base)
        helper (Intersect p1 p2)      base = Pair (helper p1 base) (helper p2 base)

-- Determine whether a plan does, indeed, answer a query.
-- NOTE: This isn't totally correct; it may return False when
--       the answer is actually True.
answersQuery :: Plan -> Query -> Bool
answersQuery p q = postCond p `implies` q
    where
        implies :: Query -> Query -> Bool
        implies a (And q1 q2) = implies a q1 && implies a q2
        implies a q = any (== q) (simpl a)

        simpl :: Query -> [Query]
        simpl (And q1 q2) = simpl q1 ++ simpl q2
        simpl x = [x]

        postCond :: Plan -> Query
        postCond All = T
        postCond None = F
        postCond (HashLookup f v) = Cmp f Eq v
        postCond (BinarySearch f cmp v) = Cmp f cmp v
        postCond (Filter p q) = And (postCond p) q
        postCond (SubPlan p1 p2) = And (postCond p1) (postCond p2)
        postCond (Intersect p1 p2) = And (postCond p1) (postCond p2)

query = And (Cmp "age" Gt "x") (Cmp "name" Eq "y")
plan1 = Intersect (BinarySearch "age" Gt "x") (HashLookup "name" "y")
plan2 = SubPlan (HashLookup "name" "y") (BinarySearch "age" Gt "x")
plan3 = Filter All query
plan4 = Filter All (Cmp "name" Eq "y")

main :: IO ()
main = do
    putStrLn $ "Query:    " ++ show query
    putStrLn $ "Plan 1:   " ++ show plan1
    putStrLn $ "    -->   structure -> " ++ show (structureFor plan1)
    putStrLn $ "    -->   valid? " ++ show (plan1 `answersQuery` query)
    putStrLn $ "Plan 2:   " ++ show plan2
    putStrLn $ "    -->   structure -> " ++ show (structureFor plan2)
    putStrLn $ "    -->   valid? " ++ show (plan2 `answersQuery` query)
    putStrLn $ "Plan 3:   " ++ show plan3
    putStrLn $ "    -->   structure -> " ++ show (structureFor plan3)
    putStrLn $ "    -->   valid? " ++ show (plan3 `answersQuery` query)
    putStrLn $ "Plan 4:   " ++ show plan4
    putStrLn $ "    -->   structure -> " ++ show (structureFor plan4)
    putStrLn $ "    -->   valid? " ++ show (plan4 `answersQuery` query)
