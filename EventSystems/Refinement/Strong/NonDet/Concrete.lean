import EventSystems.Refinement.Strong.NonDet.Basic
import EventSystems.Refinement.Functional.NonDet.Concrete

open Refinement
open FRefinement
open SRefinement

@[simp]
def newConcreteSRNDEvent [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (ev : ConcreteFRNDEventSpec v AM M α β) : ConvergentRNDEvent v AM M α β :=
  newConcreteFRNDEvent ev
