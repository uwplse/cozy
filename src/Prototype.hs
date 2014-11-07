#!/usr/bin/env runhaskell

-- Meaningful names for different things
type Type = String
type Field = String
type QueryVar = String

-- Comparison operators
data Comparison = Eq | Gt
    deriving (Show)

-- Query language
data Query =
    Cmp Field Comparison QueryVar |
    And Query Query
    deriving (Show)

-- Execution planning language
data Plan =
    HashLookup Field QueryVar |
    BinarySearch Field Comparison QueryVar |
    SubPlan Plan Plan |
    Intersect Plan Plan
    deriving (Show)

-- Data structures
data DataStructure =
    T | -- the type over which the query computes, e.g. "Record"
    MultiMap Field DataStructure |
    SortedList Field DataStructure |
    Pair DataStructure DataStructure
    deriving (Show)

structureFor :: Plan -> DataStructure
structureFor p = helper p T
    where
        helper (HashLookup f v)       base = MultiMap f base
        helper (BinarySearch f cmp v) base = SortedList f base
        helper (SubPlan p1 p2)        base = helper p1 (helper p2 base)
        helper (Intersect p1 p2)      base = Pair (helper p1 base) (helper p2 base)

query = And (Cmp "age" Gt "x") (Cmp "name" Eq "y")
plan1 = Intersect (BinarySearch "age" Gt "x") (HashLookup "name" "y")
plan2 = SubPlan (HashLookup "name" "y") (BinarySearch "age" Gt "x")

main :: IO ()
main = do
    putStrLn $ "Query:    " ++ show query
    putStrLn $ "Plan 1:   " ++ show plan1
    putStrLn $ "    -->   " ++ show (structureFor plan1)
    putStrLn $ "Plan 2:   " ++ show plan2
    putStrLn $ "    -->   " ++ show (structureFor plan2)
