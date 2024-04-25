
import EventSystems.Refinement.Strong.Basic
import EventSystems.Refinement.Functional.Concrete

open Refinement
open FRefinement
open SRefinement

structure ConcreteSREventSpec (v) [Preorder v] [WellFoundedLT v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [SRefinement AM M] (α) (β)
  extends ConcreteFREventSpec v AM M α β where

@[simp]
def newConcreteSREvent [Preorder v] [WellFoundedLT v]
                       [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
   (ev : ConcreteSREventSpec v AM M α β) : ConvergentRDetEvent v AM M α β :=
  newConcreteFREvent ev.toConcreteFREventSpec

structure ConcreteSREventSpec' (v) [Preorder v] [WellFoundedLT v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [SRefinement AM M] (α)
  extends ConcreteFREventSpec' v AM M α where

@[simp]
def newConcreteSREvent' [Preorder v] [WellFoundedLT v]
                       [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
   (ev : ConcreteSREventSpec' v AM M α) : ConvergentRDetEvent v AM M α Unit :=
  newConcreteFREvent ev.toConcreteFREventSpec

structure ConcreteSREventSpec'' (v) [Preorder v] [WellFoundedLT v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [SRefinement AM M]
  extends ConcreteFREventSpec'' v AM M where

@[simp]
def newConcreteSREvent'' [Preorder v] [WellFoundedLT v]
                       [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
   (ev : ConcreteSREventSpec'' v AM M) : ConvergentRDetEvent v AM M Unit Unit :=
  newConcreteFREvent ev.toConcreteFREventSpec
