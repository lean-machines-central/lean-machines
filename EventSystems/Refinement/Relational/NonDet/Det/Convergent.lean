
import EventSystems.Event.Ordinary
import EventSystems.Refinement.Relational.NonDet.Det.Basic
import EventSystems.Refinement.Relational.NonDet.Convergent

open Refinement

structure _AnticipatedRDetEventPO (v) [Preorder v]  [Machine ACTX AM] [Machine CTX M] [instR: Refinement AM M]
          (ev : _Event M α β) (kind : EventKind)
          extends _Variant v, _RDetEventPO (instR:=instR) ev kind  where

  nonIncreasing (m : M) (x : α):
    Machine.invariant m
    → ev.guard m x
    → let (_, m') := ev.action m x
      variant m' ≤ variant m

structure AnticipatedRDetEvent (v) [Preorder v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: Refinement AM M] (α) (β)
  extends _Event M α β where
  po : _AnticipatedRDetEventPO v (instR:=instR) to_Event (EventKind.TransDet Convergence.Anticipated)

structure AnticipatedRDetEventSpec_fromOrdinary (v) [Preorder v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [Refinement AM M] (α) (β)
  extends RDetEventSpec AM M α β where

  variant (m : M) : v

  nonIncreasing (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → let (_, m') := action m x
      variant m' ≤ variant m

@[simp]
def newAnticipatedRDetEvent_fromOrdinary [Preorder v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (ev : AnticipatedRDetEventSpec_fromOrdinary v AM M α β) : AnticipatedRDetEvent v AM M α β :=
  {
    to_Event := ev.to_Event
    po := {
      safety := ev.safety
      abstract := ev.abstract.to_NDEvent
      strengthening := ev.strengthening
      simulation := ev.simulation
      variant := ev.variant
      nonIncreasing := ev.nonIncreasing
    }
  }

structure AnticipatedRDetEventSpec_fromAnticipated (v) [Preorder v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [Refinement AM M] (α) (β)
  extends EventSpec M α β where

  abstract : AnticipatedNDEvent v AM α β

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
        ∃ am', abstract.effect am x (y, am')
               ∧ refine am' m'

  variant (m : M) : v

  nonIncreasing (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → let (_, m') := action m x
      variant m' ≤ variant m

@[simp]
def newAnticipatedRDetEvent_fromAnticipated [Preorder v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (ev : AnticipatedRDetEventSpec_fromAnticipated v AM M α β) : AnticipatedRDetEvent v AM M α β :=
  {
    to_Event := ev.to_Event
    po := {
      safety := ev.safety
      abstract := ev.abstract.to_NDEvent
      strengthening := ev.strengthening
      simulation := ev.simulation
      variant := ev.variant
      nonIncreasing := ev.nonIncreasing
    }
  }

structure _ConvergentRDetEventPO (v) [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [instR: Refinement AM M]
          (ev : _Event M α β) (kind : EventKind)
          extends _AnticipatedRDetEventPO v (instR:=instR) ev kind  where

  convergence (m : M) (x : α):
    Machine.invariant m
    → ev.guard m x
    → let (_, m') := ev.action m x
      variant m' < variant m

structure ConvergentRDetEvent (v) [Preorder v] [WellFoundedLT v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: Refinement AM M] (α) (β)
  extends _Event M α β where
  po : _ConvergentRDetEventPO v (instR:=instR) to_Event (EventKind.TransDet Convergence.Convergent)

structure ConvergentRDetEventSpec (v) [Preorder v] [WellFoundedLT v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [Refinement AM M] (α) (β)
  extends EventSpec M α β where

  abstract : _NDEvent AM α β

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
        ∃ am', abstract.effect am x (y, am')
               ∧ refine am' m'

  variant (m : M) : v

  convergence (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → let (_, m') := action m x
      variant m' < variant m

@[simp]
def newConvergentRDetEvent [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (ev : ConvergentRDetEventSpec v AM M α β) : ConvergentRDetEvent v AM M α β :=
  {
    to_Event := ev.to_Event
    po := {
      safety := ev.safety
      abstract := ev.abstract
      strengthening := ev.strengthening
      simulation := ev.simulation
      variant := ev.variant
      nonIncreasing := fun m x => by simp
                                     intros Hinv Hgrd
                                     have Hcv := ev.convergence m x Hinv Hgrd
                                     simp at Hcv
                                     exact le_of_lt Hcv
      convergence := ev.convergence
    }
  }
