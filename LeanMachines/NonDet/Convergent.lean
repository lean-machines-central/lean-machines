
import Mathlib.Order.RelClasses

import LeanMachines.Event.Convergent
import LeanMachines.NonDet.Basic
import LeanMachines.NonDet.Ordinary

/-!
## Convergent non-deterministic events

This module defines the anticipated and convergent properties
for non-deterministic events, cf. `Event.Convergent` module for
the deterministic case and common properties (e.g. what is convergence?).

-/

/-!
### Anticipated events
-/

/-- The internal representation of proof obligations for anticipated events. -/
class AnticipatedNDEventPO (v) [Preorder v] [instM:Machine CTX M] (ev : NDEvent M α β) (kind : EventKind)
          extends Variant v (instM:=instM) ev.to_EventRoot, SafeNDEventPO ev (EventKind.TransNonDet (Convergence.Anticipated))  where

  nonIncreasing (m : M) (x : α):
    Machine.invariant m
    → (grd : ev.guard m x)
    → ∀ y, ∀ m',  ev.effect m x grd (y, m')
                   → variant m' ≤ variant m

/--
The specification of a non-deterministic anticipated event.
The non-increasing argument is based on the variant type `v` assumed
to be a preorder.
-/
structure AnticipatedNDEvent (v) [Preorder v] (M) [instM : Machine CTX M]
    (α β : Type) extends OrdinaryNDEvent M α β where

  variant : M → v

  nonIncreasing (m : M) (x : α):
    Machine.invariant m
    → (grd : guard m x)
    → ∀ y, ∀ m',  effect m x grd (y, m')
                   → variant m' ≤ variant m

theorem AnticipatedNDEvent.ext [Preorder v] {CTX} {M} [Machine CTX M] {α β} (ev₁ ev₂: AnticipatedNDEvent v M α β):
  ev₁.toOrdinaryNDEvent = ev₂.toOrdinaryNDEvent
  → ev₁.variant = ev₂.variant
  → ev₁ = ev₂ :=
by
  intros Heq Hvar
  cases ev₁
  case mk m₁ ev₁ v₁ safe₁ =>
  cases ev₂
  case mk m₂ ev₂ v₂ safe₂ =>
    simp
    simp at Heq
    constructor
    · exact Heq
    · simp at Hvar
      exact Hvar

/-- A way to rebuild an Anticipated event from the required POs. -/
def mkAnticipatedNDEvent (v) [Preorder v] [Machine CTX M] (ev : NDEvent M α β)
  [instAnticipated : AnticipatedNDEventPO v ev (EventKind.TransDet (Convergence.Anticipated))] : AnticipatedNDEvent v M α β :=
  {
    effect := ev.effect
    guard := ev.guard
    safety := instAnticipated.safety
    feasibility := instAnticipated.feasibility
    nonIncreasing := instAnticipated.nonIncreasing
  }

/-- The main constructor for ordinary events. -/
@[simp]
def newAnticipatedNDEvent [Preorder v] [Machine CTX M] (ev : AnticipatedNDEvent v M α β) := ev

/-- Variant of [AnticipatedNDEvent] with Unit Output type. -/
structure AnticipatedNDEvent' (v) [Preorder v] (M) [instM : Machine CTX M]
    (α : Type) extends OrdinaryNDEvent' M α where

  variant : M → v

  nonIncreasing (m : M) (x : α):
    Machine.invariant m
    → (grd : guard m x)
    → ∀ m',  effect m x grd m'
             → variant m' ≤ variant m

instance [Preorder v] [Machine CTX M]: Coe (AnticipatedNDEvent' v M α) (AnticipatedNDEvent v M α Unit) where
  coe ev := { guard := ev.guard
              effect := fun m x grd ((), m') => ev.effect m x grd m'
              safety := fun m x Hinv Hgrd _ => ev.safety m x Hinv Hgrd
              feasibility := fun m x Hinv Hgrd => by
                simp at Hgrd
                have Hfeas := ev.feasibility m x Hinv Hgrd
                exists ()

              variant := ev.variant
              nonIncreasing := fun m x Hinv Hgrd () =>
                ev.nonIncreasing m x Hinv Hgrd
            }

@[simp]
def newAnticipatedNDEvent' [Preorder v] [Machine CTX M] (ev : AnticipatedNDEvent' v M α)
  : AnticipatedNDEvent v M α Unit :=
  newAnticipatedNDEvent ev

/-- Variant of [AnticipatedNDEvent] with Unit Output type. -/
structure AnticipatedNDEvent'' (v) [Preorder v] (M) [instM : Machine CTX M]
    extends OrdinaryNDEvent'' M where

  variant : M → v

  nonIncreasing (m : M):
    Machine.invariant m
    → (grd : guard m)
    → ∀ m',  effect m grd m'
             → variant m' ≤ variant m

instance [Preorder v] [Machine CTX M]: Coe (AnticipatedNDEvent'' v M) (AnticipatedNDEvent v M Unit Unit) where
  coe ev := { guard m _ := ev.guard m
              effect := fun m _ grd ((), m') => ev.effect m grd m'
              safety := fun m _ Hinv Hgrd _ => ev.safety m Hinv Hgrd
              feasibility := fun m _ Hinv Hgrd => by
                simp at Hgrd
                have Hfeas := ev.feasibility m Hinv Hgrd
                exists ()

              variant := ev.variant
              nonIncreasing := fun m x Hinv Hgrd () =>
                ev.nonIncreasing m Hinv Hgrd
            }


@[simp]
def newAnticipatedNDEvent'' [Preorder v] [Machine CTX M] (ev : AnticipatedNDEvent'' v M)
  : AnticipatedNDEvent v M Unit Unit :=
  newAnticipatedNDEvent ev


/-!
### Convergent events
-/

/-- The internal representation of proof obligations for anticipated events. -/
class ConvergentNDEventPO (v) [Preorder v] [WellFoundedLT v] [instM:Machine CTX M] (ev : NDEvent M α β) (kind : EventKind)
          extends Variant v (instM:=instM) ev.to_EventRoot, SafeNDEventPO ev (EventKind.TransNonDet (Convergence.Convergent))  where

  convergence (m : M) (x : α):
    Machine.invariant m
    → (grd : ev.guard m x)
    → ∀ y, ∀ m',  ev.effect m x grd (y, m')
                   → variant m' < variant m

/--
The specification of a non-deterministic convergent event.
The convergence argument is based on the variant type `v` assumed
to be a well-founded ordering.
-/
structure ConvergentNDEvent (v) [Preorder v] [WellFoundedLT v] (M) [instM : Machine CTX M]
    (α β : Type) extends OrdinaryNDEvent M α β where

  variant : M → v

  convergence (m : M) (x : α):
    Machine.invariant m
    → (grd : guard m x)
    → ∀ y, ∀ m',  effect m x grd (y, m')
                   → variant m' < variant m

instance [Preorder v] [WellFoundedLT v] [Machine CTX M]:
  Coe (ConvergentNDEvent v M α β) (AnticipatedNDEvent v M α β) where
    coe ev := {
      toOrdinaryNDEvent := ev.toOrdinaryNDEvent
      variant := ev.variant
      nonIncreasing m x Hinv Hgrd y m' Heff := by
        have Hconc := ev.convergence m x Hinv Hgrd y m' Heff
        exact le_of_lt Hconc
    }

theorem ConvergentNDEvent.ext [Preorder v] [WellFoundedLT v] {CTX} {M} [Machine CTX M] {α β} (ev₁ ev₂: ConvergentNDEvent v M α β):
  ev₁.toOrdinaryNDEvent = ev₂.toOrdinaryNDEvent
  → ev₁.variant = ev₂.variant
  → ev₁ = ev₂ :=
by
  intros Heq Hvar
  cases ev₁
  case mk m₁ ev₁ v₁ safe₁ =>
  cases ev₂
  case mk m₂ ev₂ v₂ safe₂ =>
    simp
    simp at Heq
    constructor
    · exact Heq
    · simp at Hvar
      exact Hvar

/-- A way to rebuild a Convergent event from the required POs. -/
def mkConvergentNDEvent (v) [Preorder v] [WellFoundedLT v] [Machine CTX M] (ev : NDEvent M α β)
  [instConvergent : ConvergentNDEventPO v ev (EventKind.TransNonDet (Convergence.Convergent))] : ConvergentNDEvent v M α β :=
  {
    effect := ev.effect
    guard := ev.guard
    safety := instConvergent.safety
    feasibility := instConvergent.feasibility
    convergence := instConvergent.convergence
  }

/-- The main constructor for non-deterministic convergent events. -/
@[simp]
def newConvergentNDEvent [Preorder v] [WellFoundedLT v] [Machine CTX M] (ev : ConvergentNDEvent v M α β) := ev

/-- Variant of [ConvergentNDEvent] with Unit Output type. -/
structure ConvergentNDEvent' (v) [Preorder v] [WellFoundedLT v] (M) [instM : Machine CTX M]
    (α : Type) extends OrdinaryNDEvent' M α where

  variant : M → v

  convergence (m : M) (x : α):
    Machine.invariant m
    → (grd : guard m x)
    → ∀ m',  effect m x grd m'
             → variant m' < variant m

instance [Preorder v] [WellFoundedLT v] [Machine CTX M]: Coe (ConvergentNDEvent' v M α) (ConvergentNDEvent v M α Unit) where
  coe ev := { guard := ev.guard
              effect := fun m x grd ((), m') => ev.effect m x grd m'
              safety := fun m x Hinv Hgrd _ => ev.safety m x Hinv Hgrd
              feasibility := fun m x Hinv Hgrd => by
                simp at Hgrd
                have Hfeas := ev.feasibility m x Hinv Hgrd
                exists ()

              variant := ev.variant

              convergence := fun m x Hinv Hgrd () => ev.convergence m x Hinv Hgrd
            }

@[simp]
def newConvergentNDEvent' [Preorder v] [WellFoundedLT v] [Machine CTX M] (ev : ConvergentNDEvent' v M α)
  : ConvergentNDEvent v M α Unit :=
  newConvergentNDEvent ev

/-- Variant of [AnticipatedNDEvent] with Unit Input and Output types. -/
structure ConvergentNDEvent'' (v) [Preorder v] [WellFoundedLT v] (M) [instM : Machine CTX M]
    extends OrdinaryNDEvent'' M where

  variant : M → v

  convergence (m : M):
    Machine.invariant m
    → (grd : guard m)
    → ∀ m',  effect m grd m'
             → variant m' < variant m

instance [Preorder v] [WellFoundedLT v] [Machine CTX M]: Coe (ConvergentNDEvent'' v M) (ConvergentNDEvent v M Unit Unit) where
  coe ev := { guard m _ := ev.guard m
              effect := fun m _ grd ((), m') => ev.effect m grd m'
              safety := fun m _ Hinv Hgrd _ => ev.safety m Hinv Hgrd
              feasibility := fun m _ Hinv Hgrd => by
                simp at Hgrd
                have Hfeas := ev.feasibility m Hinv Hgrd
                exists ()

              variant := ev.variant

              convergence := fun m _ Hinv Hgrd () => ev.convergence m Hinv Hgrd
            }

@[simp]
def newConvergentNDEvent'' [Preorder v] [WellFoundedLT v] [Machine CTX M] (ev : ConvergentNDEvent'' v M)
  : ConvergentNDEvent v M Unit Unit :=
  newConvergentNDEvent ev
