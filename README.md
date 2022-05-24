# MicroProver in Coq

This is a small automated theorem prover for the fragment of propositional logic consisting of implications and falsity.
The soundness and completeness of the prover has been formally verified in Coq.

The propositional symbols are named by integers.

The prover is implemented in Coq, with a command line interface in Haskell.

## Build instructions
You need Coq 8.15, Coq Equations 1.3+8.15, Haskell, and Cabal.

Before running the Haskell compiler, we need to compile the Coq code which will generate a Haskell file.
This can be done by running:
```bash
	coqc MicroProver.v
```
We can then compile the command line application by running:
```bash
	cabal build MicroProver
```
The application can then be found somewhere in the `dist-newstyle` folder.

The application can be run through Cabal by running e.g.:
```bash
	cabal run MicroProver -- "Imp (Pro 0) (Pro 0)"
```
The formulas consist of the constructors `Imp`, `False`, and `Pro n` where `n` is some integer.
Parentheses are needed around each subformula for ambiguation.

There is also a small test suite which can be run by running:
```bash
	cabal test
```
