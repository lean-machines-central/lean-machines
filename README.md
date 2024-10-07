# LeanMachines: a Lean4 framework for the modeling and refinement of stateful systems

## Overview

LeanMachines is a library for the Lean4 programming language and proof
assistant dedicated to the formal modeling of stateful systems.
The main objective is to support a stepwise refinement methodology 
inspired by the Event-B formal method but in the context of a functional
programming environment. The implementation provides the
principal Event-B constructions such as contexts, machines, events
and, most importantly, the associated refinement principles. It also
introduce extensions such as event combinators and
functional variants of the (relational) refinement principles of
Event-B. Most importantly, the framework enforces the fundamental principle of
correctness-by-construction: machine states, events structures
and refinement steps cannot be fully constructed without discharging
the prescribed proof obligations. The implementation is open source and
available for external contributions. Heavily commented examples of use are also provided.

**Important** : The framework is not directly compatible with Event-B
and related implementations such as Rodin 
(although a translator is under consideration).

## Project status : alpha

The framework is in alpha stage of development and may be modified without prior warning and without ensuring non-regression. The framework also depends on a rather "moving target": the Mathlib4 framework.

## Getting started

**As a user** :

The simplest way to experiment with the LeanMachines framework is
to add the dependency in an existing Lean4 project :

```lean
-- in the build file: lakefile.lean
require «lean-machines» from git
  "https://github.com/lean-machines-central/lean-machines.git" @ "main"
```

An example repository is available online:

https://github.com/lean-machines-central/lean-machines-examples

This provides a set of fully documented example specifications than 
can be "played with". loning this repository is probably the best way to start experimenting with he LeanMachines framework.

**As a library developer** :

To experiment with the framework implementation, the first requirement is to install the Lean4 proof assistant and the Mathlib4 library, see: <https://leanprover-community.github.io/get_started.html>

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
(please see the Mathlib4 documentation for details)

The recommended way to experiment with the framework is to use a
lean4-enabled editor: either *vscode* or *emacs*
(editor support for Lean4 is discussed in the Lean4 documentation).

## Examples of use


## Repository structure

The framework is decomposed into several modules, within the `LeanMachines` directory, structured as follows:

 - LeanMachines/Algebra : common algebraic definitions (Mathlib4 extensions)
 - LeanMachines/Event : the basic definitions : contexts, machines and deterministic events
 - EventSystem/NonDet : non-deterministic events

The refinement principles are developed in EventSystem/Refinement

 - LeanMachines/Refinement/Relational : the Event-B relational principles
 - LeanMachines/Refinement/Functional : functional abstraction
 - LeanMachines/Refinement/Strong : strong refinement for algorithmic refinement

All the examples are developed in the Examples/ directory.

## Authors and acknowledgment

The main author is Frederic Peschanski,  Sorbonne University

## License

The software is licensed (C) 2024 Frédéric Peschanski
under the Apache License 2.0  (the same as Lean4 and Mathlib4). Please see the `LICENSE` file.

