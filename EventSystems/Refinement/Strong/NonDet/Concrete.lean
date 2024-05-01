import EventSystems.Refinement.Strong.NonDet.Basic
import EventSystems.Refinement.Functional.NonDet.Concrete

open Refinement
open FRefinement
open SRefinement

structure ConcreteSRNDEventSpec (v) [Preorder v] [WellFoundedLT v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [SRefinement AM M] (α) (β)
  extends ConcreteFRNDEventSpec v AM M α β where

@[simp]
def newConcreteSRNDEvent [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (ev : ConcreteSRNDEventSpec v AM M α β) : ConvergentRNDEvent v AM M α β :=
  newConcreteFRNDEvent ev.toConcreteFRNDEventSpec

structure ConcreteSRNDEventSpec' (v) [Preorder v] [WellFoundedLT v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [SRefinement AM M] (α)
  extends ConcreteFRNDEventSpec' v AM M α where

@[simp]
def newConcreteSRNDEvent' [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (ev : ConcreteSRNDEventSpec' v AM M α) : ConvergentRNDEvent v AM M α Unit :=
  newConcreteFRNDEvent ev.toConcreteFRNDEventSpec

structure ConcreteSRNDEventSpec'' (v) [Preorder v] [WellFoundedLT v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [SRefinement AM M]
  extends ConcreteFRNDEventSpec'' v AM M where

@[simp]
def newConcreteSRNDEvent'' [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (ev : ConcreteSRNDEventSpec'' v AM M) : ConvergentRNDEvent v AM M Unit Unit :=
  newConcreteFRNDEvent ev.toConcreteFRNDEventSpec
