
import Mathlib.Order.RelClasses

import EventSystems.Convergent
import EventSystems.NonDet.Basic

/- Anticipated events -/

structure _AnticipatedNDEventPO (v) [Preorder v] [Machine CTX M] (ev : _NDEvent M α β) (kind : EventKind)
          extends _Variant v, _NDEventPO ev kind  where

  nonIncreasing (m : M) (x : α):
    Machine.invariant m
    → ev.guard m x
    → ∀ y, ∀ m',  ev.effect m x (y, m')
                   → variant m' ≤ variant m

structure AnticipatedNDEvent (v) [Preorder v] (M) [Machine CTX M] (α) (β)
          extends (_NDEvent M α β)  where
  po : _AnticipatedNDEventPO v to_NDEvent (EventKind.TransNonDet Convergence.Anticipated)

def AnticipatedNDEvent_fromOrdinary {v} [Preorder v] {M} [Machine CTX M] (ev : OrdinaryNDEvent M α β)
  (variant : M → v)
  (Hnincr: ∀ (m : M) (x : α),
    Machine.invariant m
    → ev.guard m x
    → ∀ y, ∀ m',  ev.effect m x (y, m')
                   → variant m' ≤ variant m) : AnticipatedNDEvent v M α β :=
  {
    guard := ev.guard
    effect := ev.effect
    po := {
      safety := ev.po.safety
      feasibility := ev.po.feasibility
      variant := variant
      nonIncreasing := Hnincr
    }
  }

structure AnticipatedNDEventSpec (v) [Preorder v] {CTX} (M) [Machine CTX M] (α) (β)
  extends _Variant v, NDEventSpec M α β where

  nonIncreasing (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → ∀ y, ∀ m',  effect m x (y, m')
                   → variant m' ≤ variant m

@[simp]
def newAnticipatedNDEvent {v} [Preorder v] {M} [Machine CTX M] (ev : AnticipatedNDEventSpec v M α β) : AnticipatedNDEvent v M α β :=
  AnticipatedNDEvent_fromOrdinary (newNDEvent ev.toNDEventSpec) ev.to_Variant.variant ev.nonIncreasing

/- Convergent events -/

structure _ConvergentNDEventPO (v) [Preorder v] [WellFoundedLT v] [Machine CTX M] (ev : _NDEvent M α β) (kind : EventKind)
          extends _AnticipatedNDEventPO v ev kind  where

  convergence (m : M) (x : α):
    Machine.invariant m
    → ev.guard m x
    → ∀ y, ∀ m',  ev.effect m x (y, m')
                   → variant m' < variant m

structure ConvergentNDEvent (v) [Preorder v]  [WellFoundedLT v] (M) [Machine CTX M] (α) (β)
          extends (_NDEvent M α β)  where
  po : _ConvergentNDEventPO v to_NDEvent (EventKind.TransNonDet Convergence.Convergent)

def ConvergentNDEvent_fromOrdinary  {v} [Preorder v] [WellFoundedLT v] {M} [Machine CTX M] (ev : OrdinaryNDEvent M α β)
  (variant : M → v)
  (Hconv: ∀ (m : M) (x : α),
    Machine.invariant m
    → ev.guard m x
    → ∀ y, ∀ m',  ev.effect m x (y, m')
                   → variant m' < variant m)
 : ConvergentNDEvent v M α β :=
 {
  guard := ev.guard
  effect := ev.effect
  po := {
    safety := ev.po.safety
    feasibility := ev.po.feasibility
    variant := variant
    nonIncreasing := fun m x => by simp
                                   intros Hinv Hgrd
                                   intros y m'
                                   have Hconv' := Hconv m x Hinv Hgrd y m'
                                   intro Heff
                                   apply le_of_lt
                                   exact Hconv' Heff
    convergence := Hconv
  }
 }

structure ConvergentNDEventSpec (v) [Preorder v] [WellFoundedLT v] (M) [Machine CTX M] (α) (β)
  extends _Variant v, NDEventSpec M α β where

  convergence (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → ∀ y, ∀ m',  effect m x (y, m')
                   → variant m' < variant m

@[simp]
def newConvergentNDEvent {v} [Preorder v] [WellFoundedLT v] {M} [Machine CTX M] (ev : ConvergentNDEventSpec v M α β) : ConvergentNDEvent v M α β :=
  ConvergentNDEvent_fromOrdinary (newNDEvent ev.toNDEventSpec) ev.to_Variant.variant ev.convergence

@[simp]
def ConvergentNDEvent_fromAnticipated {v} [Preorder v] [WellFoundedLT v] {M} [Machine CTX M] (ev : AnticipatedNDEvent v M α β)
    (hconv : (m : M) → (x : α)
    → Machine.invariant m
    → ev.guard m x
    → ∀ y, ∀ m',  ev.effect m x (y, m')
                   → ev.po.variant m' < ev.po.variant m) : ConvergentNDEvent v M α β :=
  {
    guard := ev.guard
    effect := ev.effect
    po := {
      safety := ev.po.safety
      feasibility := ev.po.feasibility
      variant := ev.po.variant
      nonIncreasing := ev.po.nonIncreasing
      convergence := hconv
    }
  }

/- Algebraic properties -/
