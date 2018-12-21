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
