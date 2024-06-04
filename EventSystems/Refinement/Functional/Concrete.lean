
import EventSystems.Refinement.Functional.Basic
import EventSystems.Refinement.Relational.Concrete

open Refinement
open FRefinement

structure ConcreteFREventSpec (v) [Preorder v] [WellFoundedLT v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [instFR: FRefinement AM M] (α) (β)
  extends _Variant (M:=M) v, EventSpec M α β where

  simulation (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → let (_, m') := action m x
      lift m = lift (self:=instFR)  m'

  convergence (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → let (_, m') := action m x
      variant m' < variant m

@[simp]
def ConcreteFREventSpec.toConcreteREventSpec  [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [instFR: FRefinement AM M]
  (ev : ConcreteFREventSpec v AM M α β) : ConcreteREventSpec v AM M α β :=
  {
    toEventSpec := ev.toEventSpec
    variant := ev.variant
    simulation := fun m x => by intros Hinv Hgrd am Href
                                simp [refine] at *
                                --have Href' := lift_ref (self:=instFR) m Hinv
                                --have Huniq := refine_uniq (self:=instFR) am (lift m) m Hinv Href Href'
                                have Hsim := ev.simulation m x Hinv Hgrd
                                simp at Hsim
                                rw [←Hsim]
                                assumption
    convergence := ev.convergence
  }

@[simp]
def newConcreteFREvent [Preorder v] [WellFoundedLT v]
                        [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
   (ev : ConcreteFREventSpec v AM M α β) : ConvergentRDetEvent v AM M α β :=
  newConcreteREvent ev.toConcreteREventSpec

structure ConcreteFREventSpec' (v) [Preorder v] [WellFoundedLT v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [instFR: FRefinement AM M] (α)
  extends _Variant (M:=M) v, EventSpec' M α where

  simulation (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → let m' := action m x
      lift m = lift (self:=instFR)  m'

  convergence (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → let m' := action m x
      variant m' < variant m

@[simp]
def ConcreteFREventSpec'.toConcreteFREventSpec  [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : ConcreteFREventSpec' v AM M α) : ConcreteFREventSpec v AM M α Unit :=
  {
    toEventSpec := ev.toEventSpec
    variant := ev.variant
    simulation := ev.simulation
    convergence := ev.convergence
  }

@[simp]
def newConcreteFREvent' [Preorder v] [WellFoundedLT v]
                        [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
   (ev : ConcreteFREventSpec' v AM M α) : ConvergentRDetEvent v AM M α Unit :=
  newConcreteREvent ev.toConcreteFREventSpec.toConcreteREventSpec

structure ConcreteFREventSpec'' (v) [Preorder v] [WellFoundedLT v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [instFR: FRefinement AM M]
  extends _Variant (M:=M) v, EventSpec'' M where

  simulation (m : M):
    Machine.invariant m
    → guard m
    → let m' := action m
      lift m = lift (self:=instFR)  m'

  convergence (m : M):
    Machine.invariant m
    → guard m
    → let m' := action m
      variant m' < variant m

@[simp]
def ConcreteFREventSpec''.toConcreteFREventSpec  [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : ConcreteFREventSpec'' v AM M) : ConcreteFREventSpec v AM M Unit Unit :=
  {
    toEventSpec := ev.toEventSpec
    variant := ev.variant
    simulation := fun m _ => ev.simulation m
    convergence := fun m _ => ev.convergence m
  }

@[simp]
def newConcreteFREvent'' [Preorder v] [WellFoundedLT v]
                         [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
   (ev : ConcreteFREventSpec'' v AM M) : ConvergentRDetEvent v AM M Unit Unit :=
  newConcreteREvent ev.toConcreteFREventSpec.toConcreteREventSpec
