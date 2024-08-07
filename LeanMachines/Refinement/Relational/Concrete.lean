import LeanMachines.Event.Ordinary
import LeanMachines.Event.Convergent
import LeanMachines.NonDet.Basic
import LeanMachines.Refinement.Relational.Basic
import LeanMachines.Refinement.Relational.NonDet.Det.Convergent

/-
  Concrete event, i.e. new events refining skip
  ... here generalized to support an output type β


  In the Event-B book, concrete events must be convergent
  but there are counter-arguments to consider:

  (1) the justification made in the Event-B is rather lightweight
  and not examplified

  (2) this does not seem to be enforced in Rodin, at least
  according to the Rodin Handbook v2.8

  (3) forcing convergence impacts the concrete state, which
  can be limitating in practice
  ==> see the AlarmSystem1/AddExpert event for an illustration

-/

open Refinement

structure ConcreteREventSpec (AM) [instAM: Machine ACTX AM]
                             (M) [instM: Machine CTX M]
                            [instR: Refinement AM M] (α) (β)
          extends EventSpec M α β where

  simulation (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → ∀ am, refine (self:=instR) am m
      →  refine (self:=instR) am (action m x).2

@[simp]
def newConcreteREvent [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
   (ev : ConcreteREventSpec AM M α β) : OrdinaryRDetEvent AM M α β :=
  {
    to_Event := ev.to_Event
    po := {
      lift_in := id
      lift_out := id
      safety := ev.safety
      abstract := skip_NDEvent
      strengthening := fun m x => by simp
      simulation := fun m x => by simp ; apply ev.simulation
    }
  }

/-
  XXX : some redundancy below because of a strange unification issue ...
-/

structure ConcreteREventSpec' (AM) [instAM: Machine ACTX AM]
                             (M) [instM: Machine CTX M]
                            [instR: Refinement AM M] (α)
          extends EventSpec' M α where

  simulation (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → ∀ am, refine (self:=instR) am m
      →  refine (self:=instR) am (action m x)

@[simp]
def newConcreteREvent' [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
   (ev : ConcreteREventSpec' AM M α) : OrdinaryRDetEvent AM M α Unit :=
  {
    to_Event := ev.toEventSpec.to_Event
    po := {
      lift_in := id
      lift_out := id
      safety := ev.safety
      abstract := skip_NDEvent
      strengthening := fun m x => by simp
      simulation := fun m x => by simp ; apply ev.simulation
    }
  }

structure ConcreteREventSpec'' (AM) [instAM: Machine ACTX AM]
                             (M) [instM: Machine CTX M]
                             [instR: Refinement AM M]
          extends EventSpec'' M where

  simulation (m : M):
    Machine.invariant m
    → guard m
    → ∀ am, refine (self:=instR) am m
      →  refine (self:=instR) am (action m)

@[simp]
def newConcreteREvent'' [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
   (ev : ConcreteREventSpec'' AM M) : OrdinaryRDetEvent AM M Unit Unit :=
  {
    to_Event := ev.toEventSpec.to_Event
    po := {
      lift_in := id
      lift_out := id
      safety := fun m _ => ev.safety m
      abstract := skip_NDEvent
      strengthening := fun m _ => by simp
      simulation := fun m x => by simp ; apply ev.simulation
    }
  }

/-
structure ConcreteInitREventSpec (AM) [instAM: Machine ACTX AM]
                                 (M) [instM: Machine CTX M]
                                 [instR: Refinement AM M] (α) (β) [Inhabited β]
     where

  guard (x : α) : Prop
  init (x : α) : β × M

  safety (x : α) :
    guard x
    → Machine.invariant (init x).snd

  simulation (x : α):
    guard x
    → refine (self:=instR) Machine.reset (init x).2

-- **Remark** : ConcreteInit is not possible because
-- the destination state of  Skip from Machine.reset
-- is Machine.reset, which is not a proper destination
-- state (in particular, there is no invariant enforced)

-/

structure ConcreteAnticipatedREventSpec (v) [Preorder v] [WellFoundedLT v]
                             (AM) [instAM: Machine ACTX AM]
                             (M) [instM: Machine CTX M]
                            [instR: Refinement AM M] (α) (β)
          extends _Variant (M:=M) v, ConcreteREventSpec AM M α β where

  nonIncreasing (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → let m' := (action m x).2
      variant m' ≤ variant m

@[simp]
def newConcreteAnticipatedREvent [Preorder v] [WellFoundedLT v]
                       [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
   (ev : ConcreteAnticipatedREventSpec v AM M α β) : AnticipatedRDetEvent v AM M α β :=
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
        exact ev.nonIncreasing m x Hinv Hgrd
    }
  }

/-
  XXX : some redundancy below because of a strange unification issue ...
-/

structure ConcreteAnticipatedREventSpec' (v) [Preorder v] [WellFoundedLT v]
                             (AM) [instAM: Machine ACTX AM]
                             (M) [instM: Machine CTX M]
                            [instR: Refinement AM M] (α)
          extends _Variant (M:=M) v, ConcreteREventSpec' AM M α where

  nonIncreasing (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → let m' := (action m x)
      variant m' ≤ variant m

@[simp]
def newConcreteAnticipatedREvent' [Preorder v] [WellFoundedLT v]
                       [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
   (ev : ConcreteAnticipatedREventSpec' v AM M α) : AnticipatedRDetEvent v AM M α Unit :=
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
      nonIncreasing := fun m x => by
        simp
        intros Hinv Hgrd
        exact ev.nonIncreasing m x Hinv Hgrd
    }
  }

structure ConcreteAnticipatedREventSpec'' (v) [Preorder v] [WellFoundedLT v]
                             (AM) [instAM: Machine ACTX AM]
                             (M) [instM: Machine CTX M]
                             [instR: Refinement AM M]
          extends _Variant (M:=M) v, ConcreteREventSpec'' AM M where

  nonIncreasing (m : M):
    Machine.invariant m
    → guard m
    → let m' := action m
      variant m' ≤ variant m

@[simp]
def newConcreteAnticipatedREvent'' [Preorder v] [WellFoundedLT v]
                       [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
   (ev : ConcreteAnticipatedREventSpec'' v AM M) : AnticipatedRDetEvent v AM M Unit Unit :=
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
      nonIncreasing := fun m x => by
        simp
        intros Hinv Hgrd
        exact ev.nonIncreasing m Hinv Hgrd
    }
  }

structure ConcreteConvergentREventSpec (v) [Preorder v] [WellFoundedLT v]
                             (AM) [instAM: Machine ACTX AM]
                             (M) [instM: Machine CTX M]
                            [instR: Refinement AM M] (α) (β)
          extends _Variant (M:=M) v, ConcreteREventSpec AM M α β where

  convergence (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → let m' := (action m x).2
      variant m' < variant m

@[simp]
def newConcreteConvergentREvent [Preorder v] [WellFoundedLT v]
                       [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
   (ev : ConcreteConvergentREventSpec v AM M α β) : ConvergentRDetEvent v AM M α β :=
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

structure ConcreteConvergentREventSpec' (v) [Preorder v] [WellFoundedLT v]
                             (AM) [instAM: Machine ACTX AM]
                             (M) [instM: Machine CTX M]
                            [instR: Refinement AM M] (α)
          extends _Variant (M:=M) v, ConcreteREventSpec' AM M α where

  convergence (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → let m' := (action m x)
      variant m' < variant m

@[simp]
def newConcreteConvergentREvent' [Preorder v] [WellFoundedLT v]
                       [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
   (ev : ConcreteConvergentREventSpec' v AM M α) : ConvergentRDetEvent v AM M α Unit :=
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

structure ConcreteConvergentREventSpec'' (v) [Preorder v] [WellFoundedLT v]
                             (AM) [instAM: Machine ACTX AM]
                             (M) [instM: Machine CTX M]
                             [instR: Refinement AM M]
          extends _Variant (M:=M) v, ConcreteREventSpec'' AM M where

  convergence (m : M):
    Machine.invariant m
    → guard m
    → let m' := action m
      variant m' < variant m

@[simp]
def newConcreteConvergentREvent'' [Preorder v] [WellFoundedLT v]
                       [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
   (ev : ConcreteConvergentREventSpec'' v AM M) : ConvergentRDetEvent v AM M Unit Unit :=
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
