# Event systems in Lean4

This repository contains a prototype Lean4 framework for the formal
modeling of stateful entities in the context of functional domain 
modeling.

The main objective is to support in Lean4 a stepwise refinement
of formalization, based on the refinement principles underlying
the Event-B formal method.

The implementation, a Lean4 library, provides the principal
Event-B constructions such as contexts, machines, events and,
 most importantly, the associated refinement principles.
**Important** : The framework is not directly compatible with Event-B
and related implementations such as Rodin 
(although a translator is under consideration).

## Project status : alpha

The framework is in alpha stage and may be modified without prior warning and without ensuring non-regression. If possible, the `main` branch of the repository should be useable.

## Getting started

To experiment with the framework, the first requirement is to install the Lean4 proof assistant and the Mathlib4 library, see: <https://leanprover-community.github.io/get_started.html>

The framework can be compiled using the lake tool :

```
$ lake build 
...
```

This can take a relatively long time for the first build, or when Mathlib4 receives a large update.

Because of the Mathlib4 dependency, it may be required to update the `lean-toolchain` :

```
$ lake update
...
$ cp .lake/packages/mathlib/lean-toolchain .
```

The recommended way to experiment with the framework is to "play" with
the available examples. This require either *vscode* or *emacs*
(editor support for Lean4 is discussed in the Lean4 documentation).

## Repository structure

The framework is decomposed into several modules, within the `EventSystems` directory, structured as follows:

 - EventSystems/Algebra : common algebraic definitions (Mathlib4 extensions)
 - EventSystems/Event : the basic definitions : contexts, machines and deterministic events
 - EventSystem/NonDet : non-deterministic events

The refinement principles are developed in EventSystem/Refinement

 - EventSystems/Refinement/Relational : the Event-B relational principles
 - EventSystems/Refinement/Functional : functional abstraction
 - EventSystems/Refinement/Strong : strong refinement for algorithmic refinement

All the examples are developed in the Examples/ directory.

## Authors and acknowledgment

The main author is Frederic Peschanski,  Sorbonne University

## License

The software is licensed (C) 2024 Frédéric Peschanski
under the Apache License 2.0  (the same as Lean4 and Mathlib4). Please see the `LICENSE` file.

