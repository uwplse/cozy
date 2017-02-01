# Cozy

Cozy is a tool that synthesizes collection data structure implementations
from very high-level specifications.

## Quickstart

Dependencies:
 - [Python >= 3.4](https://www.python.org/)
   (probably available in your system's package repo)
 - [Z3 Python bindings >= 4.4.2](https://github.com/Z3Prover/z3)
   (probably needs to be built from source)
 - The Python modules listed in `requirements.txt`
   (install with `pip install -r requirements.txt`)

To run the tool:

    $ python3 -m cozy --help

## Installation

You can install Cozy on your system by running

    $ ./setup.py install

(Note: you may need to install the `setuptools` package with pip first.)

The setup script works in
[the usual manner](https://packaging.python.org/distributing/#setup-py).

## Tests

The `tests` folder contains a few tests written with Python's
[unittest](https://docs.python.org/3/library/unittest.html) library. Run them
with

    python3 -m unittest tests/*.py
