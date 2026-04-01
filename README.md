# HOL4 Theorems

A collection of various HOL4 work done throughout my gradate school career.

## Organisation

The four subfolders:
- Custom Machinery: any sort of custom tactics or machinery lives here.
  The most notable bit of machinery is the ability to "quick save" and "quick load"
  states of the goal stack.
- Fundamental: Things that are "pure math" or could reasonably belong in
  existing HOL4 libraries.
- Seldonian Math: Mathematics more specific to my work: off-policy evaluation,
  seldonian algorithms, and associated lemmas.
- Seldonian Code: The part of my dissertation that requires CakeML:
  the code, a proof of the accuracy thereof.

## Version

The file are updated to CakeML job [3279](https://cakeml.org/regression.cgi/job/3279).
- CakeML: f2c8652e4819fd18e2e855bc9fa719f181ffab15
- HOL: 63f2eb9c146352dfd0bab8c5604a096d1e554d03

At present, all the HOL stuff for the work is good.
There is some cheating for some extra results in pispaceScript that aren't used
(an attempt to create an infinite-dimensional measure space).
The CakeML main-line work presently has a cheat in it as a stopgap
until something in the canonical CakeML specs is tinkered with
(see issue [1366](https://github.com/CakeML/cakeml/issues/1366)),
or until I become bold enough to try and tackle canonical specs myself.

## Canonisation

Results from here have been accepted into the HOL4 canon a few times.

For my own record-keeping and quick access if necessary:
- [1106](https://github.com/HOL-Theorem-Prover/HOL/pull/1006):
  Some measure theory results
- [1017](https://github.com/HOL-Theorem-Prover/HOL/pull/1017):
  Some integration results
- [1606](https://github.com/HOL-Theorem-Prover/HOL/pull/1606):
  Hyperbolic trigonometry library
- [1740](https://github.com/HOL-Theorem-Prover/HOL/pull/1740):
  Canonising trivialScript: sigma algebra results
- [1746](https://github.com/HOL-Theorem-Prover/HOL/pull/1746):
  Canonising trivialScript: measurable function results
- [1815](https://github.com/HOL-Theorem-Prover/HOL/pull/1815):
  Canonising trivialScript: RN derivative results
  (sort of)
