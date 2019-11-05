TIMEOUT ?= 240

%.h: %.ds
	cozy -t $(TIMEOUT) --allow-big-sets $^ --c++ $@ -p 8080 --verbose

%.bin: %.cpp %.h
	g++ -std=c++11 -O3 -Werror '$<' -o '$@'
