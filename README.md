# Schemes in Lean

The content of this repository is the result of completely refactoring the [lean-stacks-project](https://github.com/kbuzzard/lean-stacks-project), in which parts of [The Stacks Project](https://stacks.math.columbia.edu/) are formally verified using the [Lean Theorem Prover](https://leanprover.github.io/). In particular, some bits of Chapters 6, 10 and 25 are foramlized, culminating with the definition of a [scheme](https://stacks.math.columbia.edu/tag/01II). Having learnt from the many problems encountered in that first attempt, we present a cleaner and more robust approach. The main improvements are:

* The definition of a locally ringed space. Even though a scheme is technically a locally ringed space with a certain property, the previous definition, which is mathematically equivalent, did not involve locally ringed spaces.
* The use of the `is_localization` predicate, defined by Prof Neil Strickland [here](https://github.com/NeilStrickland/lean_comm_alg/blob/master/src/localization.lean), throughout instead of the concrete construction of a localized ring. Thanks to this, we avoided complicated arguments about *canonically isomorphic* rings.
* Usability. We have re-structured the previous repository and re-named all the files and many of the definitions and lemmas with the intention of providing a usable interface.

Note that this is still very much a work in progress. Some further clean-up is necessary, many proofs can be simplified and the API needs to be tested with more examples of schemes.

## Content



## Installation

To get it working, you will need Lean 3.4.2, available [here](https://github.com/leanprover/lean/releases/tag/v3.4.2). Clone the repository and type:

```
cd lean-scheme
leanpkg configure
leanpkg build
```

## Authors and acknowledgement

The main contributors to this project are:

* Kevin Buzzard ([@kbuzzard](https://github.com/kbuzzard)).
* Chris Hughes ([@ChrisHughes24](https://github.com/ChrisHughes24)).
* Kenny Lau ([@kckennylau](https://github.com/kckennylau)).
* Ramon Fernández Mir ([@ramonfmir](https://github.com/ramonfmir)).
