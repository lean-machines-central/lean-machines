
import EventSystems.Refinement.Basic
import EventSystems.Convergent

open Refinement

structure _AnticipatedREventPO (v) [Preorder v]  [Machine ACTX AM] [Machine CTX M] [instR: Refinement AM M] (ev : _Event M α β) (kind : EventKind)
          extends _Variant v, _REventPO (instR:=instR) ev kind  where

  nonIncreasing (m : M) (x : α):
    Machine.invariant m
    → ev.guard m x
    → let (_, m') := ev.action m x
      variant m' ≤ variant m

structure AnticipatedREvent (v) [Preorder v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: Refinement AM M] (α) (β) extends _Event M α β where
  po : _AnticipatedREventPO v (instR:=instR) to_Event (EventKind.TransDet Convergence.Anticipated)

structure AnticipatedREventSpecFromOrdinary (v) [Preorder v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [Refinement AM M] (α) (β)
  extends _Variant v, REventSpec AM M α β where

  nonIncreasing (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → let m' := (action m x).2
      variant m' ≤ variant m

@[simp]
def AnticipatedREvent_fromOrdinary [Preorder v]  [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (ev : OrdinaryREvent AM M α β)
  (variant : M → v)
  (Hnincr: ∀ (m : M) (x : α),
    Machine.invariant m
    → ev.guard m x
    → let (_, m') := ev.action m x
      variant m' ≤ variant m) : AnticipatedREvent v AM M α β :=
  {
    guard := ev.guard
    action := ev.action
    po := {
      safety := ev.po.safety
      abstract := ev.po.abstract
      strengthening := ev.po.strengthening
      simulation := ev.po.simulation
      variant := variant
      nonIncreasing := Hnincr
    }
  }

@[simp]
def newAnticipatedREventfromOrdinary [Preorder v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
    (ev : AnticipatedREventSpecFromOrdinary v AM M α β) : AnticipatedREvent v AM M α β :=
  AnticipatedREvent_fromOrdinary (newREvent ev.toREventSpec) ev.to_Variant.variant ev.nonIncreasing

structure AnticipatedREventSpecFromAnticipated (v) [Preorder v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [Refinement AM M] (α) (β)
  extends _Variant v (M:=M), EventSpec M α β where

  abstract : AnticipatedEvent v AM α β

  strengthening (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → ∀ am, refine am m
      → abstract.guard am x

  simulation (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → ∀ am, refine am m
      → let (y, m') := action m x
        let (z, am') := abstract.action am x
        y = z ∧ refine am' m'

  nonIncreasing (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → let m' := (action m x).2
      variant m' ≤ variant m

@[simp]
def newAnticipatedREventfromAnticipated [Preorder v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
    (ev : AnticipatedREventSpecFromAnticipated v AM M α β) : AnticipatedREvent v AM M α β :=
 {
  guard := ev.guard
  action := ev.action
  po := {
    safety := ev.safety
    variant := ev.variant
    abstract := ev.abstract.to_Event
    strengthening := ev.strengthening
    simulation := ev.simulation
    nonIncreasing := ev.nonIncreasing
  }
 }

structure _ConvergentREventPO (v) [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [instR: Refinement AM M] (ev : _Event M α β) (kind : EventKind)
          extends _AnticipatedREventPO (instR:=instR) v ev kind where

  convergence (m : M) (x : α):
    Machine.invariant m
    → ev.guard m x
    → let (_, m') := ev.action m x
      variant m' < variant m

structure ConvergentREvent (v) [Preorder v] [WellFoundedLT v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: Refinement AM M] (α) (β) extends _Event M α β where
  po : _ConvergentREventPO v (instR:=instR) to_Event (EventKind.TransDet Convergence.Convergent)

structure ConvergentREventSpec (v) [Preorder v] [WellFoundedLT v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [Refinement AM M] (α) (β)
  extends _Variant v (M:=M), EventSpec M α β where

  abstract : _Event AM α β

  strengthening (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → ∀ am, refine am m
      → abstract.guard am x

  simulation (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → ∀ am, refine am m
      → let (y, m') := action m x
        let (z, am') := abstract.action am x
        y = z ∧ refine am' m'

  convergence (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → let m' := (action m x).2
      variant m' < variant m

@[simp]
def newConvergentREvent [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (ev : ConvergentREventSpec v AM M α β) : ConvergentREvent v AM M α β :=
  {
    guard := ev.guard
    action := ev.action
    po := {
      safety := ev.safety
      abstract := ev.abstract
      strengthening := ev.strengthening
      simulation := ev.simulation
      variant := ev.variant
      nonIncreasing := fun m x => by simp
                                     intros Hinv Hgrd
                                     have Hcnv := ev.convergence m x Hinv Hgrd
                                     simp at Hcnv
                                     apply le_of_lt ; assumption
      convergence := ev.convergence
    }
  }

/-
  Concrete event, i.e. new events refining skip

  Remark : the output of the new event must be of the same
           type as the input because Skip must be refined
-/

structure ConcreteREventSpec (v) [Preorder v] [WellFoundedLT v]
                             (AM) [instAM: Machine ACTX AM]
                             (M) [instM: Machine CTX M]
                            [instR: Refinement AM M] (α)
          extends _Variant (M:=M) v where

  guard (m : M) (x : α) : Prop := True
  action (m : M) (x : α) : M
  safety (m : M) (x : α) :
    Machine.invariant m
    → guard m x
    → Machine.invariant (action m x)

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
def newConcreteREvent [Preorder v] [WellFoundedLT v]
                       [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
   (ev : ConcreteREventSpec v AM M α) : ConvergentREvent v AM M α α :=
  {
     guard := ev.guard
     action := fun m x => (x, ev.action m x)
     po := {
      safety := ev.safety
      abstract := skip_Event AM α
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
