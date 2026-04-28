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

The file are updated to CakeML job [3314](https://cakeml.org/regression.cgi/job/3314).
- CakeML: e34d19e9714f40930a36cf2387075eb2f14667f9
- HOL: 77fad203c275899bfee21faf6d2d3a66e749d7e1

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

Contributions to CakeML:
- Contributed to [1375](https://github.com/CakeML/cakeml/pull/1375):
  Edits to the CakeML inputAll function.
