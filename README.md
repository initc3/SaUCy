SaUCy [![Build Status](https://travis-ci.org/initc3/SaUCy.svg?branch=master)](https://travis-ci.org/initc3/SaUCy)
======

The Super amazing Universal Composability (SaUCy) framework aims to make
universal composability a practical tool for modular development of security
protocols.

This repository includes a Haskell implementation of the Interactive Lambda
Calculus (ILC), a newly designed process calculus that faithfully captures the
computational model underlying UC: interactive Turing machines (ITMs). ILC
adapts ITMs to a subset of the π-calculus through an affine typing
discipline. That is, *well-typed ILC programs are expressible in ITMs.* In turn,
ILC's strong confluence property enables reasoning about cryptographic security
reductions. We also use ILC to build a concrete, executable (preliminary)
implementation of the UC framework.

More details about ILC and SaUCy can be found in our
[paper](https://eprint.iacr.org/2019/402.pdf).

This repository is still work in progress. Stay tuned for more details.

Install
-------

1. Install [Haskell platform](https://www.haskell.org/platform/).
2. Run 'stack build'.

Run
---
To run the ILC interactive interpreter, run 'stack exec -- saucy'.
To run the ILC interpreter on an ILC program, run 'stack exec -- saucy <FILE>'.