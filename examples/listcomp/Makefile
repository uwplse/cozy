TIMEOUT ?= 240

%.h: %.ds
	cozy -t $(TIMEOUT) --allow-big-sets $^ --c++ $@ --save synthesized/$^.$(TIMEOUT).synthesized

%.bin: %.cpp %.h
	g++ -std=c++11 -O3 -Werror -Wno-parentheses-equality '$<' -o '$@'

all: ListSums.bin SelectMany.bin SumMul.bin
