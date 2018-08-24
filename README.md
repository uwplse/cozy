# Cozy

[![Build Status](https://travis-ci.org/CozySynthesizer/cozy.svg?branch=master
)](https://travis-ci.org/CozySynthesizer/cozy)

Cozy is a tool that synthesizes data structure implementations
from simple high-level specifications. It automatically chooses a good
representation of your data and efficient method implementations.

Cozy can greatly simplify the task of
writing software modules with private state.
In most cases, Cozy specifications are short and self-documenting, and are
therefore much easier to maintain than handwritten implementations.
Occasionally Cozy can discover deep optimizations that human
developers shy away from.

Currently, Cozy can generate code for C++ and Java.

## Quickstart

Dependencies:
 - [Python >= 3.5](https://www.python.org/)
 - The Python modules listed in `requirements.txt`;
   install them with `pip3 install -r requirements.txt`.

If you run into trouble, consult the wiki page on [troubleshooting
setup and installation](https://github.com/CozySynthesizer/cozy/wiki/Troubleshooting-setup-and-installation).

To list all command-line options (and ensure that everything is correctly
installed):

    $ git clone git@github.com:CozySynthesizer/cozy.git
    $ cd cozy
    $ pip3 install -r requirements.txt
    $ python3 -m cozy --help

To synthesize an implementation (`Basic.java`) of the specification
`examples/basic.ds`:

    $ python3 -m cozy examples/basic.ds --java Basic.java

## The `cozy` executable

If you want to install the global executable
`cozy` on your system:

    $ pip3 install .

Installation is optional; Cozy can run in this source directory as described
in the "Quickstart" section.  Running `cozy [ARGS]` behaves just like
`python3 -m cozy [ARGS]` would.

## More Information

 - [User manual](https://github.com/CozySynthesizer/cozy/wiki/User-Manual)
 - [Information for developers](https://github.com/CozySynthesizer/cozy/wiki/Information-for-Developers)
