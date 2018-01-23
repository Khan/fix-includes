#!/usr/bin/env python

from setuptools import setup

setup(
    name='fix-includes',
    version='0.1',
    description=('Fix-includes manages include/import/require lines in '
                 'C, C++, Python, and JavaScript (node.js).'),
    author='Craig Silverstein',
    author_email='csilvers+fix_includes@gmail.com',
    url='https://github.com/csilvers/fix-includes',
    keywords=['import', 'include', 'python', 'nodejs'],
    packages=['fix_includes'],
    scripts=[
        'fix_includes/fix_includes.py',
        'fix_includes/fix_js_requires.py',
        'fix_includes/fix_python_imports.py',
    ],
    classifiers=[
        ('License :: OSI Approved :: University of Illinois/'
         'NCSA Open Source License'),
        'Programming Language :: Python :: 2',
        'Programming Language :: Python :: 2.7',
    ],
)
