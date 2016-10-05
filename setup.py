#!/usr/bin/env python3

import os
import shutil
import sys
from distutils.core import setup

def die(msg):
    print(msg, file=sys.stderr)
    sys.exit(1)

if sys.version_info < (3, 4):
    die("Need Python >= 3.4; found {}".format(sys.version))

try:
    import z3
    if z3.get_version() < (4, 4, 2):
        die("Need Z3 >= 4.4.2; found {}".format(z3.get_version_string()))
except ImportError:
    die("Z3 Python module was not found")

os.makedirs("build/exes", exist_ok=True)
shutil.copy("cozy.py", "build/exes/cozy")

with open("requirements.txt") as f:
    reqs = [line.strip() for line in f]

setup(
    name='Cozy',
    version='2.0-alpha',
    description='Data Structure Synthesizer',
    author='Calvin Loncaric',
    author_email='loncaric@cs.washington.edu',
    url='https://cozy.uwplse.org/',
    packages=['cozy'],
    scripts=['build/exes/cozy'],
    requires=reqs,
    )
