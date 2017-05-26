# Cozy

Cozy is a tool that synthesizes a wide range of data structure implementations
from very high-level specifications. It can greatly simplify the task of
writing software modules with private state since it chooses a good
representation of your data and efficient method implementations automatically.
In some cases, Cozy can apply abstraction-breaking optimizations that human
developers normally don't, such as using [intrusive data structures](https://stackoverflow.com/questions/5004162/what-does-it-mean-for-a-data-structure-to-be-intrusive).

## Quickstart

Dependencies:
 - [Python >= 3.4](https://www.python.org/)
 - [Z3 >= 4.5](https://github.com/Z3Prover/z3) (with Python 3 bindings)
 - The Python modules listed in `requirements.txt`
   (install with `pip install -r requirements.txt`)

To list all command-line options (and ensure that everything is correctly
installed):

    $ python3 -m cozy --help

To synthesize an implementation of `specs/basic.ds` as Basic.java:

    $ python3 -m cozy specs/basic.ds --java Basic.java

## Installation

Installation is optional; Cozy can run in this source directory as described
in the "Quickstart" section. If you want to install the global executable
"cozy" on your system:

    $ ./setup.py install

(Note: you may need to install the `setuptools` package with pip first.)

The setup script works in
[the usual manner](https://packaging.python.org/distributing/#setup-py).

## Writing Specifications

At the moment, there is no formal documentation on Cozy's input language.
Sorry! The `specs` folder has a number of example inputs that you can use as
templates, and the most complete description of the grammar is the parser
itself (`cozy/parse.py`).

## Tests

The `tests` folder contains a few tests written with Python's
[unittest](https://docs.python.org/3/library/unittest.html) library. Run them
with

    $ python3 -m unittest -b tests/*.py

(The `-b` flag "buffers" output so that Python only shows output from failing
tests.)
