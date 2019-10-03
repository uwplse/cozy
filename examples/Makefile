# build and run some examples

MaxBag.java: maxbag.ds
	cozy maxbag.ds --java MaxBag.java

LSort.java: lsort.ds
	cozy lsort.ds --java LSort.java --guava

guava-23.0.jar:
	wget https://search.maven.org/remotecontent?filepath=com/google/guava/guava/23.0/guava-23.0.jar -O $@

%.class: %.java guava-23.0.jar
	javac -cp .:* $<

java: MaxBag.class MaxBagMain.class LSort.class

TIMEOUT ?= 240

listcomp.h: listcomp-flatmap.ds
	cozy -t $(TIMEOUT) --allow-big-sets listcomp-flatmap.ds --c++ listcomp.h -p 8080 --verbose --save listcomp.synthesized

select.h: select-flatmap.ds
	cozy -t $(TIMEOUT) --allow-big-sets select-flatmap.ds --c++ select.h -p 8080 --verbose --save select.synthesized

select: select.cpp select.h
	g++ -std=c++11 -O3 -Werror '$<' -o '$@'

listcomp: listcomp.cpp listcomp.h
	g++ -std=c++11 -O3 -Werror '$<' -o '$@'

run-select: select
	time ./select

run-listcomp: listcomp
	time ./listcomp
