
import Mathlib.Order.RelClasses

import LeanMachines.Event.Convergent
import LeanMachines.NonDet.Basic
import LeanMachines.NonDet.Ordinary

/-!
## Convergent deterministic events

This module defines the anticipated and convergent properties
for non-deterministic events, cf. `Event.Convergent` module for
the deterministic case and common properties (e.g. what is convergence?).

-/

/-!
### Anticipated events
-/

/-- The internal representation of proof obligations for anticipated events. -/
structure _AnticipatedNDEventPO (v) [Preorder v] [instM:Machine CTX M] (ev : _NDEvent M α β) (kind : EventKind)
          extends _Variant v (instM:=instM), _NDEventPO ev kind  where

  nonIncreasing (m : M) (x : α):
    Machine.invariant m
    → (grd : ev.guard m x)
    → ∀ y, ∀ m',  ev.effect m x grd (y, m')
                   → variant m' ≤ variant m

/-- The type of non-deterministic anticipated events.
It is an event for machine type `M` with input type `α` and output type `β`.
The non-increasing argument is based on the variant type `v` assumed
to be a preorder. -/
structure AnticipatedNDEvent (v) [Preorder v] (M) [Machine CTX M] (α) (β)
          extends (_NDEvent M α β)  where
  po : _AnticipatedNDEventPO v to_NDEvent (EventKind.TransNonDet Convergence.Anticipated)

/-- The "downgrading" of an anticipated event to an ordinary one. -/
@[simp]
def AnticipatedNDEvent.toOrdinaryNDEvent [Preorder v] [Machine CTX M]
  (ev : AnticipatedNDEvent v M α β) : OrdinaryNDEvent M α β :=
  {
    to_NDEvent := ev.to_NDEvent
    po := {
      safety := ev.po.safety
      feasibility := ev.po.feasibility
    }
  }


@[simp]
private def AnticipatedNDEvent_fromOrdinary {v} [Preorder v] {M} [Machine CTX M] (ev : OrdinaryNDEvent M α β)
  (variant : M → v)
  (Hnincr: ∀ (m : M) (x : α),
    Machine.invariant m
    → (grd : ev.guard m x)
    → ∀ y, ∀ m',  ev.effect m x grd (y, m')
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

/-- The specification of a non-deterministic, anticipated event for machine `M`
with input type `α` and output type `β`. The non-increasing proof relies
 on a variant type `v` assumed to be a preorder.
Note that the guard, effect and safety PO of the event must be also
specified, as in the ordinary case (cf. `OrdinaryNDEventSpec`).
  -/
structure AnticipatedNDEventSpec (v) [Preorder v] {CTX} (M) [instM:Machine CTX M] (α) (β)
  extends _Variant v (instM:=instM), NDEventSpec M α β where
  /-- Proof obligation: the variant is non-increasing. -/
  nonIncreasing (m : M) (x : α):
    Machine.invariant m
    → (grd : guard m x)
    → ∀ y, ∀ m',  effect m x grd (y, m')
                   → variant m' ≤ variant m

/-- Construction of an anticipated non-deterministic event from a
`AnticipatedNDEventSpec` specification. -/
@[simp]
def newAnticipatedNDEvent [Preorder v] [Machine CTX M] (ev : AnticipatedNDEventSpec v M α β) : AnticipatedNDEvent v M α β :=
  AnticipatedNDEvent_fromOrdinary (newNDEvent ev.toNDEventSpec) ev.to_Variant.variant ev.nonIncreasing

/-- Variant of `AnticipatedNDEventSpec` with implicit `Unit` output type -/
structure AnticipatedNDEventSpec' (v) [Preorder v] {CTX} (M) [instM:Machine CTX M] (α)
  extends _Variant v (instM:=instM), NDEventSpec' M α where

  nonIncreasing (m : M) (x : α):
    Machine.invariant m
    → (grd : guard m x)
    → ∀ m',  effect m x grd m'
             → variant m' ≤ variant m

@[simp]
def AnticipatedNDEventSpec'.toAnticipatedNDEventSpec [Preorder v] [Machine CTX M]
  (ev : AnticipatedNDEventSpec' v M α) : AnticipatedNDEventSpec v M α Unit :=
  {
    toNDEventSpec := ev.toNDEventSpec
    variant := ev.variant
    nonIncreasing := fun m x => by simp
                                   intros Hinv Hgrd m' Heff
                                   apply ev.nonIncreasing m x Hinv Hgrd ; assumption
  }

/-- Variant of `newAnticipatedNDEvent` with implicit `Unit` output type -/
@[simp]
def newAnticipatedNDEvent' [Preorder v] [Machine CTX M] (ev : AnticipatedNDEventSpec' v M α) : AnticipatedNDEvent v M α Unit :=
  newAnticipatedNDEvent ev.toAnticipatedNDEventSpec

/-- Variant of `AnticipatedNDEventSpec` with implicit `Unit` input and output types -/
structure AnticipatedNDEventSpec'' (v) [Preorder v] {CTX} (M) [instM:Machine CTX M]
  extends _Variant v (instM:=instM), NDEventSpec'' M where

  nonIncreasing (m : M):
    Machine.invariant m
    → (grd : guard m)
    → ∀ m',  effect m grd m'
             → variant m' ≤ variant m

@[simp]
def AnticipatedNDEventSpec''.toAnticipatedNDEventSpec [Preorder v] [Machine CTX M]
  (ev : AnticipatedNDEventSpec'' v M) : AnticipatedNDEventSpec v M Unit Unit :=
  {
    toNDEventSpec := ev.toNDEventSpec
    variant := ev.variant
    nonIncreasing := fun m x => by simp
                                   intros Hinv Hgrd m' Heff
                                   apply ev.nonIncreasing m Hinv Hgrd ; assumption
  }

/-- Variant of `newAnticipatedNDEvent` with implicit `Unit` input and output types -/
@[simp]
def newAnticipatedNDEvent'' [Preorder v] [Machine CTX M] (ev : AnticipatedNDEventSpec'' v M) : AnticipatedNDEvent v M Unit Unit :=
  newAnticipatedNDEvent ev.toAnticipatedNDEventSpec

/-!
### Convergent events
-/

/-- The internal representation of proof obligations for convergent events. -/
structure _ConvergentNDEventPO (v) [Preorder v] [WellFoundedLT v] [Machine CTX M] (ev : _NDEvent M α β) (kind : EventKind)
          extends _AnticipatedNDEventPO v ev kind  where

  convergence (m : M) (x : α):
    Machine.invariant m
    → (grd : ev.guard m x)
    → ∀ y, ∀ m',  ev.effect m x grd (y, m')
                   → variant m' < variant m

/-- The type of non-deterministic convergent events.
It is an event for machine type `M` with input type `α` and output type `β`.
The convergence argument is based on the variant type `v` assumed
to be a well-founded preorder. -/
structure ConvergentNDEvent (v) [Preorder v]  [WellFoundedLT v] (M) [Machine CTX M] (α) (β)
          extends (_NDEvent M α β)  where
  po : _ConvergentNDEventPO v to_NDEvent (EventKind.TransNonDet Convergence.Convergent)

/-- The "downgrading" of a convergent event to an anticipated one. -/
@[simp]
def ConvergentNDEvent.toAnticipatedNDEvent [Preorder v] [WellFoundedLT v] [Machine CTX M]
  (ev : ConvergentNDEvent v M α β) : AnticipatedNDEvent v M α β :=
  {
    to_NDEvent := ev.to_NDEvent
    po := {
      safety := ev.po.safety
      feasibility := ev.po.feasibility
      variant := ev.po.variant
      nonIncreasing := ev.po.nonIncreasing
    }
  }


private def ConvergentNDEvent_fromOrdinary  {v} [Preorder v] [WellFoundedLT v] {M} [Machine CTX M] (ev : OrdinaryNDEvent M α β)
  (variant : M → v)
  (Hconv: ∀ (m : M) (x : α),
    Machine.invariant m
    → (grd : ev.guard m x)
    → ∀ y, ∀ m',  ev.effect m x grd (y, m')
                   → variant m' < variant m)
 : ConvergentNDEvent v M α β :=
 {
  guard := ev.guard
  effect := ev.effect
  po := {
    safety := ev.po.safety
    feasibility := ev.po.feasibility
    variant := variant
    nonIncreasing := fun m x => by --simp
                                   intros Hinv Hgrd
                                   intros y m'
                                   have Hconv' := Hconv m x Hinv Hgrd y m'
                                   intro Heff
                                   apply le_of_lt
                                   exact Hconv' Heff
    convergence := Hconv
  }
 }

/-- The specification of a non-deterministic, convergent event for machine `M`
with input type `α` and output type `β`. The convergence proof relies
 on a variant type `v` assumed to be a well-founded preorder.
Note that the guard, action and safety PO of the event must be also
specified, as in the ordinary case (cf. `OrdinaryNDEventSpec`).
  -/
structure ConvergentNDEventSpec (v) [Preorder v] [WellFoundedLT v] (M) [instM:Machine CTX M] (α) (β)
  extends _Variant v (instM:=instM), NDEventSpec M α β where
  /-- Proof obligation: the variant is strictly decreasing. -/
  convergence (m : M) (x : α):
    Machine.invariant m
    → (grd : guard m x)
    → ∀ y, ∀ m',  effect m x grd (y, m')
                   → variant m' < variant m

/-- Construction of a convergent non-deterministic event from a
`ConvergentNDEventSpec` specification. -/
@[simp]
def newConvergentNDEvent {v} [Preorder v] [WellFoundedLT v] {M} [Machine CTX M] (ev : ConvergentNDEventSpec v M α β) : ConvergentNDEvent v M α β :=
  ConvergentNDEvent_fromOrdinary (newNDEvent ev.toNDEventSpec) ev.to_Variant.variant ev.convergence

@[simp]
private def ConvergentNDEvent_fromAnticipated {v} [Preorder v] [WellFoundedLT v] {M} [Machine CTX M] (ev : AnticipatedNDEvent v M α β)
    (hconv : (m : M) → (x : α)
    → Machine.invariant m
    → (grd : ev.guard m x)
    → ∀ y, ∀ m',  ev.effect m x grd (y, m')
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

/-- Variant of `ConvergentNDEventSpec` with implicit `Unit` output type -/
structure ConvergentNDEventSpec' (v) [Preorder v] [WellFoundedLT v] (M) [instM:Machine CTX M] (α)
  extends _Variant v (instM:=instM), NDEventSpec' M α where

  convergence (m : M) (x : α):
    Machine.invariant m
    → (grd : guard m x)
    → ∀ m',  effect m x grd m'
             → variant m' < variant m

@[simp]
def ConvergentNDEventSpec'.toConvergentNDEventSpec [Preorder v] [WellFoundedLT v] {M} [Machine CTX M]
  (ev : ConvergentNDEventSpec' v M α) : ConvergentNDEventSpec v M α Unit :=
  {
    toNDEventSpec := ev.toNDEventSpec
    variant := ev.variant
    convergence := fun m x => by simp
                                 intros Hinv Hgrd m' Heff
                                 apply ev.convergence <;> assumption
  }

/-- Variant of `newConvergentNDEvent` with implicit `Unit` output type -/
@[simp]
def newConvergentNDEvent' [Preorder v] [WellFoundedLT v] [Machine CTX M] (ev : ConvergentNDEventSpec' v M α) : ConvergentNDEvent v M α Unit :=
  newConvergentNDEvent ev.toConvergentNDEventSpec

/-- Variant of `ConvergentNDEventSpec` with implicit `Unit` input and output types -/
structure ConvergentNDEventSpec'' (v) [Preorder v] [WellFoundedLT v] (M) [instM:Machine CTX M]
  extends _Variant v (instM:=instM), NDEventSpec'' M where

  convergence (m : M):
    Machine.invariant m
    → (grd : guard m)
    → ∀ m',  effect m grd m'
             → variant m' < variant m

@[simp]
def ConvergentNDEventSpec''.toConvergentNDEventSpec [Preorder v] [WellFoundedLT v] [Machine CTX M]
  (ev : ConvergentNDEventSpec'' v M) : ConvergentNDEventSpec v M Unit Unit :=
  {
    toNDEventSpec := ev.toNDEventSpec
    variant := ev.variant
    convergence := fun m x => by simp
                                 intros Hinv Hgrd m' Heff
                                 apply ev.convergence <;> assumption
  }

/-- Variant of `newConvergentEvent` with implicit `Unit` input and output types -/
@[simp]
def newConvergentNDEvent'' [Preorder v] [WellFoundedLT v] [Machine CTX M] (ev : ConvergentNDEventSpec'' v M) : ConvergentNDEvent v M Unit Unit :=
  newConvergentNDEvent ev.toConvergentNDEventSpec
