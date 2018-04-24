#!/usr/bin/env python3

import os
import sys
from setuptools import setup, find_packages

def die(msg):
    print(msg, file=sys.stderr)
    sys.exit(1)

if sys.version_info < (3, 5):
    die("Need Python >= 3.5; found {}".format(sys.version))

try:
    import z3
    if z3.get_version() < (4, 5):
        die("Need Z3 >= 4.5; found {}".format(z3.get_version_string()))
except ImportError:
    die("Z3 Python module was not found")

with open(os.path.join(os.path.dirname(__file__), "requirements.txt")) as f:
    reqs = [line.strip() for line in f]

setup(
    name='Cozy',
    version='2.0a1',
    description='Data Structure Synthesizer',
    author='Calvin Loncaric',
    author_email='loncaric@cs.washington.edu',
    url='https://cozy.uwplse.org/',
    packages=find_packages(),
    entry_points = { "console_scripts": "cozy=cozy.main:run" },
    install_requires=reqs,
    )
