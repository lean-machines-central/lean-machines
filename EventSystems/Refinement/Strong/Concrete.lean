
import EventSystems.Refinement.Strong.Basic
import EventSystems.Refinement.Functional.Concrete

open Refinement
open FRefinement
open SRefinement

@[simp]
def newConcreteSREvent [Preorder v] [WellFoundedLT v]
                       [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
   (ev : ConcreteFREventSpec v AM M α β) : ConvergentRDetEvent v AM M α β :=
  newConcreteFREvent ev

@[simp]
def newConcreteSREvent' [Preorder v] [WellFoundedLT v]
                       [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
   (ev : ConcreteFREventSpec' v AM M α) : ConvergentRDetEvent v AM M α Unit :=
  newConcreteFREvent ev.toConcreteFREventSpec

@[simp]
def newConcreteSREvent'' [Preorder v] [WellFoundedLT v]
                       [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
   (ev : ConcreteFREventSpec'' v AM M) : ConvergentRDetEvent v AM M Unit Unit :=
  newConcreteFREvent ev.toConcreteFREventSpec
