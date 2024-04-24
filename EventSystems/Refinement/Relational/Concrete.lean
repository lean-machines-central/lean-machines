import EventSystems.Event.Ordinary
import EventSystems.Event.Convergent
import EventSystems.NonDet.Basic
import EventSystems.Refinement.Relational.Basic
import EventSystems.Refinement.Relational.NonDet.Det.Convergent

/-
  Concrete event, i.e. new events refining skip
  ... here generalized to support an output type β

-/

open Refinement

structure ConcreteEventSpec (v) [Preorder v] [WellFoundedLT v]
                             (AM) [instAM: Machine ACTX AM]
                             (M) [instM: Machine CTX M]
                            [instR: Refinement AM M] (α) (β)
          extends _Variant (M:=M) v, EventSpec M α β where

  simulation (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → ∀ am, refine (self:=instR) am m
      →  refine (self:=instR) am (action m x).2

  convergence (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → let m' := (action m x).2
      variant m' < variant m

@[simp]
def newConcreteEvent [Preorder v] [WellFoundedLT v]
                       [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
   (ev : ConcreteEventSpec v AM M α β) : ConvergentRDetEvent v AM M α β :=
  {
    to_Event := ev.to_Event
    po := {
      safety := ev.safety
      abstract := skip_NDEVent
      strengthening := fun m x => by simp
      simulation := fun m x => by simp ; apply ev.simulation
      variant := ev.variant
      nonIncreasing := fun m x => by simp
                                     intros Hinv Hgrd
                                     have Hcv := ev.convergence m x Hinv Hgrd
                                     simp at Hcv
                                     exact le_of_lt Hcv
      convergence := ev.convergence
    }
  }


/-
  XXX : some redundancy below because of a strange unification issue ...
-/

structure ConcreteEventSpec' (v) [Preorder v] [WellFoundedLT v]
                             (AM) [instAM: Machine ACTX AM]
                             (M) [instM: Machine CTX M]
                            [instR: Refinement AM M] (α)
          extends _Variant (M:=M) v, EventSpec' M α where

  simulation (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → ∀ am, refine (self:=instR) am m
      →  refine (self:=instR) am (action m x)

  convergence (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → let m' := (action m x)
      variant m' < variant m

@[simp]
def newConcreteEvent' [Preorder v] [WellFoundedLT v]
                       [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
   (ev : ConcreteEventSpec' v AM M α) : ConvergentRDetEvent v AM M α Unit :=
  {
    to_Event := ev.toEventSpec.to_Event
    po := {
      safety := ev.safety
      abstract := skip_NDEVent
      strengthening := fun m x => by simp
      simulation := fun m x => by simp ; apply ev.simulation
      variant := ev.variant
      nonIncreasing := fun m x => by simp
                                     intros Hinv Hgrd
                                     have Hcv := ev.convergence m x Hinv Hgrd
                                     simp at Hcv
                                     exact le_of_lt Hcv
      convergence := ev.convergence
    }
  }

structure ConcreteEventSpec'' (v) [Preorder v] [WellFoundedLT v]
                             (AM) [instAM: Machine ACTX AM]
                             (M) [instM: Machine CTX M]
                             [instR: Refinement AM M]
          extends _Variant (M:=M) v, EventSpec'' M where

  simulation (m : M):
    Machine.invariant m
    → guard m
    → ∀ am, refine (self:=instR) am m
      →  refine (self:=instR) am (action m)

  convergence (m : M):
    Machine.invariant m
    → guard m
    → let m' := action m
      variant m' < variant m

@[simp]
def newConcreteEvent'' [Preorder v] [WellFoundedLT v]
                       [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
   (ev : ConcreteEventSpec'' v AM M) : ConvergentRDetEvent v AM M Unit Unit :=
  {
    to_Event := ev.toEventSpec.to_Event
    po := {
      safety := fun m _ => ev.safety m
      abstract := skip_NDEVent
      strengthening := fun m x => by simp
      simulation := fun m x => by simp ; apply ev.simulation
      variant := ev.variant
      nonIncreasing := fun m x => by simp
                                     intros Hinv Hgrd
                                     have Hcv := ev.convergence m Hinv Hgrd
                                     simp at Hcv
                                     exact le_of_lt Hcv
      convergence := fun m _ => ev.convergence m
    }
  }
