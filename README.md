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

To synthesize an implementation (`Basic.java`) of the specification
`specs/basic.ds`:

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

The `specs` folder has a number of example specifications that you can use as
templates. The most complete description of the grammar is the parser itself
(`cozy/parse.py`).

Cozy specifications always have this general shape:

    MyDataStructure:

        state elements : Bag<Int>

        query size()
            len elements

        query containsZero()
            exists [x | x <- elements, x == 0]

        op addElement(x : Int)
            elements.add(x);

The `state` declarations declare the private state of the data structure.
The `query` methods retrieve some information about the private state.
The `op` methods alter the private state.

From a specification like this, Cozy will produce a much better implementation:

    MyDataStructure:

        state sz : Int
        state ctz : Bool

        query size()
            sz

        query containsZero()
            ctz

        op addElement(x : Int)
            sz = sz + 1;
            ctz = ctz or (x == 0);

### Supported Types

 - `Bool`: booleans
 - `Int`: 32-bit integers
 - `String`: strings
 - `(T1, T2, ...)`: tuples, e.g. `(Int, Int)` is a pair of ints
 - `{f1 : T1, f2 : T2, ...}`: records
 - `Set<T>`, `Bag<T>`: sets and multisets, respectively
 - `enum {case1, case2, ...}`: enumerations

### Query Methods

Expressions may contain:

 - Boolean operators (`and`, `or`, `not`)
 - Linear arithmetic (`+`, `-`)
 - Ternary expressions (`cond ? x : y`)
 - List comprehensions (`[expr | x <- xs, y <- ys, predicate]`)
 - Field access (`tuple.0` to read the first element of a tuple, `record.field`
   to read a field of a record)
 - Set union (`xs + ys`) and difference (`xs - ys`)

Cozy supports many useful reduction operations on collections as well:

 - Sum (`sum xs`)
 - Length (`len xs`, equivalent to `sum [1 | x <- xs]`)
 - Determine whether a collection is empty (`empty xs`, equivalent to
   `len xs == 0`)
 - Determine whether a collection has any elements (`exists xs`, equivalent to
   `not empty xs`)
 - Determine whether all elements of a boolean collection are true (`all xs`,
   equivalent to `empty [x | x <- xs, x == false]`)
 - Determine whether some element of a boolean collection is true (`any xs`,
   equivalent to `exists [x | x <- xs, x == true]`)
 - Find distinct elements (`distinct xs`)
 - Determine whether a xs's elements are all unique
   (`unique xs`, equivalent to `xs == distinct xs`)
 - Get the single element from a singleton collection (`the xs`)
 - Determine whether an element is in a collection (`e in xs`, equivalent to
   `exists [x | x <- xs, x == e]`)
 - Find the smallest or largest element (`min xs` or `max xs`, respectively)
 - Find an element that minimizes or maximizes a function (`argmin {\user -> user.signupDate} users` or `argmax ...`)

### Update Methods

For all types of state, assignment is allowed: `x = new_value;`.

For records, changes can be made to individual fields: `x.field = new_value;`.

For sets and bags, Cozy allows `x.add(new_element);` and `x.remove(element);`.
Note that `remove` removes exactly one occurrence of the element if
any is present.

Updates can also be guarded by if-checks, as in `if condition { x.add(y); }`.

An update method may perform multiple updates in sequence, as in

    op update_with(y : Int)
        xs.add(y);
        if (y > 0) { s = s + y; }

### Other Useful Features

#### Typedefs

Cozy supports typedefs to make specifications easier to read.

    MyDataStructure:
        type MyStruct = { a : Int, b : Int }
        ...

#### Assumptions

Sometimes clients interact with a data structure in more refined ways. For
instance, it might happen to be true that a client will never add a duplicate
element to the data structure. Cozy cannot possibly infer these facts during
synthesis.

Assumptions allow specification writers to communicate facts about the client
to Cozy. They can be added to both update and query methods. Cozy does not
check them; instead, it assumes that they will be true at each call site. That
means it is up to you, the developer, to ensure that your assumptions are
correct!

In this example, the query `empty` will always return false under the given
assumption. Cozy can exploit this fact to produce the trivial, obvious
implementation.

    MyDataStructure:
        state ints : Bag<Int>
        op add(i : Int)
            assume i > 0;
            ints.add(i);
        query empty()
            assume not empty ints;
            empty ints

#### Invariants

Invariants are properties of the data structure state that will always be true.
Cozy _does_ check invariants by ensuring that (1) they hold in the initial
state when all collections are empty and (2) every update operation preserves
them.

For instance:

    MyDataStructure:
        state ints : Bag<Int>

        // invariant: all stored numbers are positive
        assume all [i > 0 | i <- ints];

        op add(i : Int)
            // This assumption is necessary to ensure that the
            // invariant is preserved. Cozy will complain if it
            // is missing!
            assume i > 0;
            ints.add(i);

#### Handles

(TODO: this is very complicated!)

#### Escaping the Spec Language

To facilitate integration with other code, Cozy gives you several ways to
"escape" the confines of the specification language. This lets you use types,
functions, and other features defined outside the specification.

Code enclosed in double-braces at the top or bottom of a specification will be
copied into the output directly. For example, to put a synthesized class into
a particular Java package:

    {{
    package com.mypackage;
    }}

    MyDataStructure:
        ...

    {{
    /* here is a footer! */
    }}

To use a type declared elsewhere, you can use `Native "TypeName"`. At code
generation time, Cozy will simply insert the text `TypeName` wherever that type
is used. For instance:

    MyDataStructure:
        type User = Native "User"
        state u : User
        ...

To use code declared elsewhere, you can use "extern" functions. These are
snippets of code that Cozy inlines into the final implementation where
necessary. Cozy assumes that these snippets are both effectively pure and quite
efficient. For instance, Cozy's limited support for strings can be easily
extended:

    MyDataStructure:
        type Char = Native "char"
        extern firstCharacter(s : String) : Char = "{s}.charAt(0)"
        extern isUpperCase(c : Char) : Bool = "Character.isUpperCase({c})"

        state names : Set<String>

        query miscapitalized()
            [n | n <- names, not isUpperCase(firstCharacter(n))]

## Tests

The `tests` folder contains a few tests written with Python's
[unittest](https://docs.python.org/3/library/unittest.html) library. Run them
with

    $ python3 -m unittest -b tests/*.py

(The `-b` flag "buffers" output so that Python only shows output from failing
tests.)
