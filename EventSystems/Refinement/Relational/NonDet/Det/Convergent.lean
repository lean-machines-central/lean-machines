
import EventSystems.Event.Ordinary
import EventSystems.Refinement.Relational.Convergent
import EventSystems.Refinement.Relational.NonDet.Det.Basic
import EventSystems.Refinement.Relational.NonDet.Convergent

open Refinement

structure _AnticipatedRDetEventPO (v) [Preorder v]  [Machine ACTX AM] [Machine CTX M] [instR: Refinement AM M]
          (ev : _Event M α β) (kind : EventKind) (α' β')
          extends _Variant v, _RDetEventPO (instR:=instR) ev kind α' β'  where

  nonIncreasing (m : M) (x : α):
    Machine.invariant m
    → ev.guard m x
    → let (_, m') := ev.action m x
      variant m' ≤ variant m

structure AnticipatedRDetEvent (v) [Preorder v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: Refinement AM M]
  (α) (β) (α':=α) (β':=β) extends _Event M α β where
  po : _AnticipatedRDetEventPO v (instR:=instR) to_Event (EventKind.TransDet Convergence.Anticipated) α' β'

structure AnticipatedRDetEventSpec (v) [Preorder v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [Refinement AM M]
  {α β α' β'} (abstract : _NDEvent AM α' β')
  extends _Variant v, RDetEventSpec AM M (α:=α) (β:=β) (α':=α') (β':=β') abstract where

  nonIncreasing (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → let (_, m') := action m x
      variant m' ≤ variant m

@[simp]
private def _newAnticipatedRDetEvent [Preorder v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : _NDEvent AM α' β') (ev : AnticipatedRDetEventSpec v AM M (α:=α) (β:=β) (α':=α') (β':=β') abs) : AnticipatedRDetEvent v AM M α β α' β' :=
  {
    to_Event := ev.to_Event
    po := {
      safety := ev.safety
      lift_in := ev.lift_in
      lift_out := ev.lift_out
      abstract := abs
      strengthening := ev.strengthening
      simulation := ev.simulation
      variant := ev.variant
      nonIncreasing := ev.nonIncreasing
    }
  }

@[simp]
def newAnticipatedRDetEventfromOrdinary [Preorder v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : OrdinaryNDEvent AM α' β') (ev : AnticipatedRDetEventSpec v AM M (α:=α) (β:=β) (α':=α') (β':=β') abs.to_NDEvent) : AnticipatedRDetEvent v AM M α β α' β' :=
  _newAnticipatedRDetEvent abs.to_NDEvent ev

@[simp]
def newAnticipatedRDetEventfromOrdinary' [Preorder v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : OrdinaryNDEvent AM α' Unit) (ev : AnticipatedRDetEventSpec v AM M (α:=α) (β:=Unit) (α':=α') (β':=Unit) abs.to_NDEvent) : AnticipatedRDetEvent v AM M α Unit α' Unit :=
  _newAnticipatedRDetEvent abs.to_NDEvent ev

@[simp]
def newAnticipatedRDetEventfromOrdinary'' [Preorder v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : OrdinaryNDEvent AM Unit Unit) (ev : AnticipatedRDetEventSpec v AM M (α:=Unit) (β:=Unit) (α':=Unit) (β':=Unit) abs.to_NDEvent) : AnticipatedRDetEvent v AM M Unit Unit :=
  _newAnticipatedRDetEvent abs.to_NDEvent ev

@[simp]
def newAnticipatedRDetEventfromAnticipated [Preorder v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : AnticipatedNDEvent v AM α' β') (ev : AnticipatedRDetEventSpec v AM M (α:=α) (β:=β) (α':=α') (β':=β') abs.to_NDEvent) : AnticipatedRDetEvent v AM M α β α' β' :=
  _newAnticipatedRDetEvent abs.to_NDEvent ev

@[simp]
def newAnticipatedRDetEventfromAnticipated' [Preorder v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : AnticipatedNDEvent v AM α' Unit) (ev : AnticipatedRDetEventSpec v AM M (α:=α) (β:=Unit) (α':=α') (β':=Unit) abs.to_NDEvent) : AnticipatedRDetEvent v AM M α Unit α' Unit :=
  _newAnticipatedRDetEvent abs.to_NDEvent ev

@[simp]
def newAnticipatedRDetEventfromAnticipated'' [Preorder v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : AnticipatedNDEvent v AM Unit Unit) (ev : AnticipatedRDetEventSpec v AM M (α:=Unit) (β:=Unit) (α':=Unit) (β':=Unit) abs.to_NDEvent) : AnticipatedRDetEvent v AM M Unit Unit :=
  _newAnticipatedRDetEvent abs.to_NDEvent ev

structure _ConvergentRDetEventPO (v) [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [instR: Refinement AM M]
          (ev : _Event M α β) (kind : EventKind) (α' β')
          extends _AnticipatedRDetEventPO v (instR:=instR) ev kind α' β' where

  convergence (m : M) (x : α):
    Machine.invariant m
    → ev.guard m x
    → let (_, m') := ev.action m x
      variant m' < variant m

structure ConvergentRDetEvent (v) [Preorder v] [WellFoundedLT v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: Refinement AM M]
  (α) (β) (α':=α) (β':=β) extends _Event M α β where
  po : _ConvergentRDetEventPO v (instR:=instR) to_Event (EventKind.TransDet Convergence.Convergent) α' β'


@[simp]
def ConvergentRDetEvent.toConvergentEvent [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [instR: Refinement AM M]
  (ev : ConvergentRDetEvent v AM M α β α' β') : ConvergentEvent v M α β :=
  {
    to_Event := ev.to_Event
    po := {
      to_EventPO := ev.po.to_AnticipatedRDetEventPO.to_EventPO
      variant := ev.po.variant
      nonIncreasing := ev.po.nonIncreasing
      convergence := ev.po.convergence
    }
  }

structure ConvergentRDetEventSpec (v) [Preorder v] [WellFoundedLT v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [Refinement AM M]
  {α β α' β'} (abstract : _NDEvent AM α' β')
  extends _Variant v, RDetEventSpec AM M (α:=α) (β:=β) (α':=α') (β':=β') abstract where

  convergence (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → let (_, m') := action m x
      variant m' < variant m

@[simp]
def newConvergentRDetEvent [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : _NDEvent AM α' β') (ev : ConvergentRDetEventSpec v AM M (α:=α) (β:=β) (α':=α') (β':=β') abs) : ConvergentRDetEvent v AM M α β α' β' :=
  {
    to_Event := ev.to_Event
    po := {
      safety := ev.safety
      abstract := abs
      strengthening := ev.strengthening
      simulation := ev.simulation
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

@[simp]
def newConvergentRDetEvent' [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : _NDEvent AM α' Unit) (ev : ConvergentRDetEventSpec v AM M (α:=α) (β:=Unit) (α':=α') (β':=Unit) abs) : ConvergentRDetEvent v AM M α Unit α' Unit :=
  newConvergentRDetEvent abs ev

@[simp]
def newConvergentRDetEvent'' [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : _NDEvent AM Unit Unit) (ev : ConvergentRDetEventSpec v AM M (α:=Unit) (β:=Unit) (α':=Unit) (β':=Unit) abs) : ConvergentRDetEvent v AM M Unit Unit :=
  newConvergentRDetEvent abs ev
