import LeanMachines.Refinement.Strong.NonDet.Basic
import LeanMachines.Refinement.Functional.NonDet.Concrete

open Refinement
open FRefinement
open SRefinement

@[simp]
def newConcreteSRNDEvent [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (ev : ConcreteFRNDEventSpec v AM M α β) : ConvergentRNDEvent v AM M α β :=
  newConcreteFRNDEvent ev

@[simp]
def newConcreteSRNDEvent' [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (ev : ConcreteFRNDEventSpec' v AM M α) : ConvergentRNDEvent v AM M α Unit :=
  newConcreteSRNDEvent ev.toConcreteFRNDEventSpec

@[simp]
def newConcreteSRNDEvent'' [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (ev : ConcreteFRNDEventSpec'' v AM M) : ConvergentRNDEvent v AM M Unit Unit :=
  newConcreteSRNDEvent ev.toConcreteFRNDEventSpec
