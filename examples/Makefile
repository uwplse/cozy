# build and run some examples

MaxBag.java: maxbag.ds
	cozy maxbag.ds --java MaxBag.java

%.class: %.java
	javac $<

java: MaxBag.class MaxBagMain.class
