import EventSystems.Event.Ordinary
import EventSystems.Event.Convergent
import EventSystems.Refinement.Relational.Basic

/-
  Concrete event, i.e. new events refining skip
  ... here generalized to support an output type β

-/

open Refinement

structure ConcreteREventSpec (v) [Preorder v] [WellFoundedLT v]
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
def newConcreteREvent [Preorder v] [WellFoundedLT v]
                       [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
   (ev : ConcreteREventSpec v AM M α β) : ConvergentREvent v AM M α β :=
  {
     guard := ev.guard
     action := fun m x => (ev.output m x, ev.action m x)
     po := {
      safety := ev.safety
      abstract := funskip_Event AM ev.output
      strengthening := fun m x => by simp
      simulation := fun m x => by simp
                                  intros Hinv Hgrd am Href
                                  apply ev.simulation m x Hinv Hgrd am Href
      variant := ev.variant
      nonIncreasing := fun m x => by simp
                                     intros Hinv Hgrd
                                     have Hcv := ev.convergence m x Hinv Hgrd
                                     apply le_of_lt ; assumption
      convergence := ev.convergence
     }
  }

structure ConcreteREventSpec'' (v) [Preorder v] [WellFoundedLT v]
                             (AM) [instAM: Machine ACTX AM]
                             (M) [instM: Machine CTX M]
                            [instR: Refinement AM M]
          extends _Variant (M:=M) v where

  guard (m : M) : Prop := True
  action (m : M) : M
  safety (m : M) :
    Machine.invariant m
    → guard m
    → Machine.invariant (action m)

  simulation (m : M):
    Machine.invariant m
    → guard m
    → ∀ am, refine (self:=instR) am m
      →  refine (self:=instR) am (action m)

  convergence (m : M):
    Machine.invariant m
    → guard m
    → let m' := (action m)
      variant m' < variant m

@[simp]
def ConcreteREventSpec_from_ConcreteREventSpec'' [Preorder v] [WellFoundedLT v]
                       [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
    (ev : ConcreteREventSpec'' v AM M) : ConcreteREventSpec v AM M Unit :=
  {
    guard := fun m () => ev.guard m
    action := fun m () => ev.action m
    safety := fun m () => ev.safety m
    simulation := fun m () => ev.simulation m
    convergence := fun m () => ev.convergence m
  }

@[simp]
def newConcreteREvent'' [Preorder v] [WellFoundedLT v]
                       [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
   (ev : ConcreteREventSpec'' v AM M) : ConvergentREvent v AM M Unit Unit :=
   newConcreteREvent (ConcreteREventSpec_from_ConcreteREventSpec'' ev)
