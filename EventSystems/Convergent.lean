
import Mathlib.Order.RelClasses

import EventSystems.Basic

structure _Variant (v) [Preorder v] [Machine CTX M] where
  variant : M → v

/- Anticipated events -/

structure _AnticipatedEventPO (v) [Preorder v] [Machine CTX M] (ev : _Event M α β) (kind : EventKind)
          extends _Variant v, _EventPO ev kind  where

  nonIncreasing (m : M) (x : α):
    Machine.invariant m
    → ev.guard m x
    → let (_, m') := ev.action m x
      variant m' ≤ variant m

structure AnticipatedEvent (v) [Preorder v] (M) [Machine CTX M] (α) (β)
          extends (_Event M α β)  where
  po : _AnticipatedEventPO v to_Event (EventKind.TransDet Convergence.Anticipated)

def AnticipatedEvent_fromOrdinary {v} [Preorder v] {M} [Machine CTX M] (ev : OrdinaryEvent M α β)
  (variant : M → v)
  (Hnincr: ∀ (m : M) (x : α),
    Machine.invariant m
    → ev.guard m x
    → let (_, m') := ev.action m x
      variant m' ≤ variant m) : AnticipatedEvent v M α β :=
  {
    guard := ev.guard
    action := ev.action
    po := {
      safety := ev.po.safety
      variant := variant
      nonIncreasing := Hnincr
    }
  }

structure AnticipatedEventSpec (v) [Preorder v] {CTX} (M) [Machine CTX M] (α) (β)
  extends _Variant v, EventSpec M α β where

  nonIncreasing (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → let m' := (action m x).2
      variant m' ≤ variant m

@[simp]
def newAnticipatedEvent {v} [Preorder v] {M} [Machine CTX M] (ev : AnticipatedEventSpec v M α β) : AnticipatedEvent v M α β :=
  AnticipatedEvent_fromOrdinary (newEvent ev.toEventSpec) ev.to_Variant.variant ev.nonIncreasing

/- Convergent events -/

structure _ConvergentEventPO (v) [Preorder v] [WellFoundedLT v] [Machine CTX M] (ev : _Event M α β) (kind : EventKind)
          extends _AnticipatedEventPO v ev kind  where

  convergence (m : M) (x : α):
    Machine.invariant m
    → ev.guard m x
    → let (_, m') := ev.action m x
      variant m' < variant m

structure ConvergentEvent (v) [Preorder v]  [WellFoundedLT v] (M) [Machine CTX M] (α) (β)
          extends (_Event M α β)  where
  po : _ConvergentEventPO v to_Event (EventKind.TransDet Convergence.Convergent)

def ConvergentEvent_fromOrdinary  {v} [Preorder v] [WellFoundedLT v] {M} [Machine CTX M] (ev : OrdinaryEvent M α β)
  (variant : M → v)
  (Hconv: ∀ (m : M) (x : α),
    Machine.invariant m
    → ev.guard m x
    → let m' := (ev.action m x).2
      variant m' < variant m)
 : ConvergentEvent v M α β :=
 {
  guard := ev.guard
  action := ev.action
  po := {
    safety := ev.po.safety
    variant := variant
    nonIncreasing := fun m x => by simp
                                   intros Hinv Hgrd
                                   have Hconv' := Hconv m x Hinv Hgrd
                                   apply le_of_lt
                                   exact Hconv'
    convergence := Hconv
  }
 }

structure ConvergentEventSpec (v) [Preorder v] [WellFoundedLT v] (M) [Machine CTX M] (α) (β)
  extends _Variant v, EventSpec M α β where

  convergence (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → let m' := (action m x).2
      variant m' < variant m

@[simp]
def newConvergentEvent {v} [Preorder v] [WellFoundedLT v] {M} [Machine CTX M] (ev : ConvergentEventSpec v M α β) : ConvergentEvent v M α β :=
  ConvergentEvent_fromOrdinary (newEvent ev.toEventSpec) ev.to_Variant.variant ev.convergence

@[simp]
def ConvergentEvent_fromAnticipated {v} [Preorder v] [WellFoundedLT v] {M} [Machine CTX M] (ev : AnticipatedEvent v M α β)
    (hconv : (m : M) → (x : α)
    → Machine.invariant m
    → ev.guard m x
    → let m' := (ev.action m x).2
      ev.po.variant m' < ev.po.variant m) : ConvergentEvent v M α β :=
  {
    guard := ev.guard
    action := ev.action
    po := {
      safety := ev.po.safety
      variant := ev.po.variant
      nonIncreasing := ev.po.nonIncreasing
      convergence := hconv
    }
  }

/- Algebraic properties -/

def mapAnticipatedEvent [Preorder v] [Machine CTX M] (f : α → β) (ev : AnticipatedEvent v M γ α) : AnticipatedEvent v M γ β :=
  newAnticipatedEvent {
    guard := ev.guard
    action := fun m x => let (y, m') := ev.action m x
                         (f y, m')
    safety :=  ev.po.safety
    variant := ev.po.variant
    nonIncreasing := ev.po.nonIncreasing
  }

instance [Preorder v] [Machine CTX M] : Functor (AnticipatedEvent v M γ) where
  map := mapAnticipatedEvent

instance [Preorder v] [Machine CTX M] : LawfulFunctor (AnticipatedEvent v M γ) where
  map_const := rfl
  id_map := by intros ; rfl
  comp_map := by intros ; rfl

def mapConvergentEvent [Preorder v] [WellFoundedLT v] [Machine CTX M] (f : α → β) (ev : ConvergentEvent v M γ α) : ConvergentEvent v M γ β :=
  newConvergentEvent {
    guard := ev.guard
    action := fun m x => let (y, m') := ev.action m x
                         (f y, m')
    safety :=  ev.po.safety
    variant := ev.po.variant
    convergence := ev.po.convergence
  }

instance [Preorder v] [WellFoundedLT v] [Machine CTX M] : Functor (ConvergentEvent v M γ) where
  map := mapConvergentEvent

instance [Preorder v] [WellFoundedLT v] [Machine CTX M] : LawfulFunctor (ConvergentEvent v M γ) where
  map_const := rfl
  id_map := by intros ; rfl
  comp_map := by intros ; rfl
