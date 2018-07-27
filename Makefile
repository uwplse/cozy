
.SUFFIXES:
.PHONY: all

all: exp.pickle
	time python3 synth.py

exp.pickle: cozy/state_maintenance.py
	time python3 -m cozy.state_maintenance
