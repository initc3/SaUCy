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

Installation
------------

1. Install [Haskell platform](https://www.haskell.org/platform/).
2. Run `stack build`.

Running ILC Programs
--------------------
The ILC implementation includes an interactive environment, in which ILC
expressions can be interactively evaluated and programs can be interpreted. You
can fire up the interactive environment with the command `stack exec -- saucy`.

Here's a summary of commands available:

| Command | Description |
| --- | --- |
| `:load <FILE>` | Load ILC source file |
| `:browse` | List all variables in scope with their type signatures |
| `:type <EXPR>` | Print type of ILC expression |
| `:quit` | Quit |

ILC source files can also be executed with the command `stack exec -- saucy
<FILE>`.