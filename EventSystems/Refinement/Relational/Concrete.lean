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
   (ev : ConcreteREventSpec v AM M α β) : ConvergentRDetEvent v AM M α β :=
  {
    to_Event := ev.to_Event
    po := {
      lift_in := id
      lift_out := id
      safety := ev.safety
      abstract := skip_NDEvent
      strengthening := fun m x => by simp
      simulation := fun m x => by simp ; apply ev.simulation
      variant := ev.variant
      nonIncreasing := fun m x => by
        simp
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

structure ConcreteREventSpec' (v) [Preorder v] [WellFoundedLT v]
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
def newConcreteREvent' [Preorder v] [WellFoundedLT v]
                       [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
   (ev : ConcreteREventSpec' v AM M α) : ConvergentRDetEvent v AM M α Unit :=
  {
    to_Event := ev.toEventSpec.to_Event
    po := {
      lift_in := id
      lift_out := id
      safety := ev.safety
      abstract := skip_NDEvent
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

structure ConcreteREventSpec'' (v) [Preorder v] [WellFoundedLT v]
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
def newConcreteREvent'' [Preorder v] [WellFoundedLT v]
                       [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
   (ev : ConcreteREventSpec'' v AM M) : ConvergentRDetEvent v AM M Unit Unit :=
  {
    to_Event := ev.toEventSpec.to_Event
    po := {
      lift_in := id
      lift_out := id
      safety := fun m _ => ev.safety m
      abstract := skip_NDEvent
      strengthening := fun m _ => by simp
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

structure ConcreteRInitEventSpec (AM) [instAM: Machine ACTX AM]
                                 (M) [instM: Machine CTX M]
                                 [instR: Refinement AM M] (α) (β) [Inhabited β]
     where

  guard (x : α) : Prop
  init (x : α) : β × M

  safety (x : α) :
    Machine.invariant (init x).snd

  simulation (x : α):
    refine (self:=instR) Machine.reset (init x).2

@[simp]
def newConcreteRInitEvent [Machine ACTX AM] [Machine CTX M] [Refinement AM M] [Inhabited β]
   (ev : ConcreteRInitEventSpec AM M α β) : InitRDetEvent AM M α β :=
  {
    guard := fun _ x => ev.guard x
    action := fun _ x => ev.init x
    po := {
      lift_in := id
      lift_out := id
      safety := fun x => by simp
                            intro _
                            apply ev.safety x
      abstract := {
        to_NDEvent := skip_InitNDEvent
        po := {
          safety := fun x => by
            intros _ _ m' Heff
            simp at Heff
            rw [Heff]
            have Href := ev.simulation x
            apply refine_safe Machine.reset (ev.init x).2
            apply ev.safety
            assumption

          feasibility := fun _ => by simp
        }
      }
      strengthening := fun m _ => by simp
      simulation := fun x => by
        simp
        intros _ am Href
        exists Machine.reset
        have Hres := refine_reset (M:=M) am Href
        simp [Hres]
        apply ev.simulation
    }
  }

structure ConcreteRInitEventSpec' (AM) [instAM: Machine ACTX AM]
                                 (M) [instM: Machine CTX M]
                                 [instR: Refinement AM M] (α)
     where

  guard (x : α) : Prop
  init (x : α) : M

  safety (x : α) :
    Machine.invariant (init x)

  simulation (x : α):
    refine (self:=instR) Machine.reset (init x)

@[simp]
def ConcreteRInitEventSpec'.toConcreteRInitEventSpec [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (ev : ConcreteRInitEventSpec' AM M α) : ConcreteRInitEventSpec AM M α Unit :=
  {
    init := fun x => ((), ev.init x)
    guard := ev.guard
    safety := ev.safety
    simulation := ev.simulation
  }

@[simp]
def newConcreteRInitEvent' [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
   (ev : ConcreteRInitEventSpec' AM M α) : InitRDetEvent AM M α Unit :=
  newConcreteRInitEvent ev.toConcreteRInitEventSpec

structure ConcreteRInitEventSpec'' (AM) [instAM: Machine ACTX AM]
                                   (M) [instM: Machine CTX M]
                                   [instR: Refinement AM M]
     where

  guard : Prop
  init : M

  safety :
    Machine.invariant init

  simulation (x : α):
    refine (self:=instR) Machine.reset init

@[simp]
def ConcreteRInitEventSpec''.toConcreteRInitEventSpec [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (ev : ConcreteRInitEventSpec'' AM M) : ConcreteRInitEventSpec AM M Unit Unit :=
  {
    guard := fun () => ev.guard
    init := fun () => ((), ev.init)
    safety := fun () => ev.safety
    simulation := ev.simulation
  }

@[simp]
def newConcreteRInitEvent'' [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
   (ev : ConcreteRInitEventSpec'' AM M) : InitRDetEvent AM M Unit Unit :=
  newConcreteRInitEvent ev.toConcreteRInitEventSpec
