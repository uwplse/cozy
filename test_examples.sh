#!/bin/bash

set -x
set -e

function test_example {
  cozy $1.ds --c++ $2 --java $3 --simple
  g++ -std=c++11 -c $2
  rm $2
  javac -cp .:* $3
  rm $3
}

function test_example_1min_guava {
  cozy $1.ds --c++ $2 --java $3 --timeout 60 --guava
  g++ -std=c++11 -c $2
  rm $2
  javac -cp .:* $3
  rm $3
}

cd examples
make guava-23.0.jar

#test_example ztopo-cache ztopo-cozy.cpp TileCache.java
test_example basic basic.cpp Basic.java
test_example disjunction disjunction.cpp In.java
test_example graph graph.cpp Graph.java
test_example map map.cpp Map.java
#test_example nonscalar-tuple nonscalar-tuple.cpp Example.java
test_example read-after-write read-after-write.cpp ReadAfterWrite.java
#test_example sat4j-literal-storage sat4j-literal-storage.cpp SynthesizedLitStorage.java
test_example agg agg.cpp Aggr.java
test_example boundsbug2 boundsbug2.cpp BoundsBug2.java
#test_example docstring wordbag.cpp WordBag.java
test_example in in.cpp In.java
test_example maxbag maxbag.cpp MaxBag.java
#test_example openfire-roster roster-core.cpp RosterCore.java
#test_example redmine redmine.cpp Redmine.java # too slow now
test_example tpchq5 tpchq5.cpp TPCHQ5.java
#test_example argmin argmin.cpp MinFinder.java
test_example clausedb clausedb.cpp ClauseDB.java
test_example func func.cpp Structure.java
test_example intset intset.cpp ClauseDB.java
test_example nested-map nested-map.cpp In.java
test_example polyupdate polyupdate.cpp Polyupdate.java
test_example_1min_guava lsort lsort.cpp LSort.java
#test_example rot1 rot1.cpp Rot1.java

# TODO: fix the commented out examples
