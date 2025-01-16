
import LeanMachines.NonDet.Basic
import LeanMachines.NonDet.Convergent
import LeanMachines.Refinement.Relational.NonDet.Basic

/-!

# Convergent refined non-deterministic events

This module defines the construction of anticipated and
convergent refind non-deterministic events.

-/

open Refinement

/-!
## Anticipated events
-/

/-- Internal representation of proof obligations for anticipated events -/
structure _AnticipatedRNDEventPO (v) [Preorder v]  [@Machine ACTX AM] [instM:@Machine CTX M] [instR: Refinement AM M]
  (ev : _NDEvent M α β) (kind : EventKind) (α') (β')
          extends _Variant v (instM:=instM), _RNDEventPO (instR:=instR) ev kind α' β'  where

  nonIncreasing (m : M) (x : α):
    Machine.invariant m
    → (grd : ev.guard m x)
    → ∀ y, ∀ m', ev.effect m x grd (y, m')
                → variant m' ≤ variant m

/-- The representation of anticipated non-deterministic refined events, constructed
by specifications structures, e.g. `AnticipatedRNDEventSpec`,
 and smart constructors, e.g. `newAnticipatedRNDEvent`. -/
structure AnticipatedRNDEvent (v) [Preorder v] (AM) [@Machine ACTX AM] (M) [@Machine CTX M] [instR: Refinement AM M]
  (α β) (α':=α) (β':=β)
  extends _NDEvent M α β where
  po : _AnticipatedRNDEventPO v (instR:=instR) to_NDEvent (EventKind.TransDet Convergence.Anticipated) α' β'

@[simp]
def AnticipatedRNDEvent.toAnticipatedNDEvent [Preorder v] [@Machine ACTX AM] [@Machine CTX M] [Refinement AM M]
  (ev : AnticipatedRNDEvent v AM M α β α' β') : AnticipatedNDEvent v M α β :=
  { to_NDEvent := ev.to_NDEvent
    po := {
      safety := ev.po.safety
      feasibility := ev.po.feasibility
      variant := ev.po.variant
      nonIncreasing := ev.po.nonIncreasing
    }
  }

/-- Specification of non-deterministic anticipated refined events.
with: `v` a variant type assumed to be pre-ordered,
 `AM` the abstact machine type, `M` the concrete maching type,
 `α` the concrete input parameter type, `α'` the corresponding abstract input type (by default, `α`)
 `β` the concrete input parameter type, `β'` the corresponding abstract input type (by default, `β`)
The `abs` parameter is the ordinary event intended to be refined, which must be non-deterministic.

Note that `abs` should be, in practice, either an ordinary event or an anticipated one.
An abstract convergent event should be refined as a convergent event.

The input and output types can be lifted to the abstract, if needed,
 using the `lift_in` and `lift_out` components.

The added proof obligation, beyond `safety` , guard `strengthening`,
abstract event `simulation`, is a `nonIncreasing` requirement.
 -/
structure AnticipatedRNDEventSpec (v) [Preorder v] (AM) [@Machine ACTX AM] (M) [instM:@Machine CTX M] [Refinement AM M]
  {α β α' β'} (abs : OrdinaryNDEvent AM α' β')
  extends _Variant v (instM:=instM), RNDEventSpec AM M (α:=α) (β:=β) (α':=α') (β':=β') abs where

  /-- Proof obligation: the variant does not increases. -/
  nonIncreasing (m : M) (x : α):
    Machine.invariant m
    → (grd : guard m x)
    → ∀ y, ∀ m', effect m x grd (y, m')
                 → variant m' ≤ variant m

@[simp]
private def _newAnticipatedRNDEvent [Preorder v] [@Machine ACTX AM] [@Machine CTX M] [Refinement AM M]
  (abs : OrdinaryNDEvent AM α' β') (ev : AnticipatedRNDEventSpec v AM M (α:=α) (β:=β) (α':=α') (β':=β') abs) : AnticipatedRNDEvent v AM M α β α' β' :=
  {
    to_NDEvent := ev.to_NDEvent
    po := {
      safety := ev.safety
      feasibility := ev.feasibility
      lift_in := ev.lift_in
      lift_out := ev.lift_out
      abstract := abs.to_NDEvent
      strengthening := ev.strengthening
      simulation := ev.simulation
      variant := ev.variant
      nonIncreasing := ev.nonIncreasing
    }
  }

/-- Smart constructor for anticipated refined event,
with: `abs` the ordinary event to refine, and
  `ev` the refined event specification, which must be ordinary
  (cf. `AnticipatedRNDEventSpec`).
-/
@[simp]
def newAnticipatedRNDEventfromOrdinary [Preorder v] [@Machine ACTX AM] [@Machine CTX M] [Refinement AM M]
  (abs : OrdinaryNDEvent AM α' β') (ev : AnticipatedRNDEventSpec v AM M (α:=α) (β:=β) (α':=α') (β':=β') abs) : AnticipatedRNDEvent v AM M α β α' β' :=
  _newAnticipatedRNDEvent abs ev

/-- Variant of `newAnticipatedRNDEventfromOrdinary` for anticipated events. -/
@[simp]
def newAnticipatedRNDEventfromAnticipated [Preorder v] [@Machine ACTX AM] [@Machine CTX M] [Refinement AM M]
  (abs : AnticipatedNDEvent v AM α' β') (ev : AnticipatedRNDEventSpec v AM M (α:=α) (β:=β) (α':=α') (β':=β') abs.toOrdinaryNDEvent) : AnticipatedRNDEvent v AM M α β α' β' :=
  _newAnticipatedRNDEvent abs.toOrdinaryNDEvent ev

/-- Variant of `AnticipatedRNDEventSpec` with implicit `Unit` output type -/
structure AnticipatedRNDEventSpec' (v) [Preorder v] (AM) [@Machine ACTX AM] (M) [instM:@Machine CTX M] [Refinement AM M]
  {α α'} (abs : OrdinaryNDEvent AM α' Unit)
  extends _Variant v (instM:=instM), RNDEventSpec' AM M (α:=α) (α':=α') abs where

  nonIncreasing (m : M) (x : α):
    Machine.invariant m
    → (grd : guard m x)
    → ∀ m', effect m x grd m'
            → variant m' ≤ variant m

@[simp]
def AnticipatedRNDEventSpec'.toAnticipatedRNDEventSpec [Preorder v] [@Machine ACTX AM] [@Machine CTX M] [Refinement AM M]
  (abs : OrdinaryNDEvent AM α' Unit)
  (ev : AnticipatedRNDEventSpec' v AM M (α:=α) (α':=α') abs): AnticipatedRNDEventSpec v AM M (α:=α) (β:=Unit) (α':=α') (β':=Unit) abs :=
  {
    toRNDEventSpec := ev.toRNDEventSpec
    variant := ev.variant
    nonIncreasing:= fun m x => by simp ; apply ev.nonIncreasing
  }

/-- Variant of `newAnticipatedRNDEventFromOrdinary` with implicit `Unit` output type -/
@[simp]
def newAnticipatedRNDEventfromOrdinary' [Preorder v] [@Machine ACTX AM] [@Machine CTX M] [Refinement AM M]
  (abs : OrdinaryNDEvent AM α' Unit) (ev : AnticipatedRNDEventSpec' v AM M (α:=α) (α':=α') abs) : AnticipatedRNDEvent v AM M α Unit α' Unit :=
  _newAnticipatedRNDEvent abs ev.toAnticipatedRNDEventSpec

/-- Variant of `newAnticipatedRNDEventFromAnticipated` with implicit `Unit` output type -/
@[simp]
def newAnticipatedRNDEventfromAnticipated' [Preorder v] [@Machine ACTX AM] [@Machine CTX M] [Refinement AM M]
  (abs : AnticipatedNDEvent v AM α' Unit) (ev : AnticipatedRNDEventSpec' v AM M (α:=α) (α':=α') abs.toOrdinaryNDEvent) : AnticipatedRNDEvent v AM M α Unit α' Unit :=
  _newAnticipatedRNDEvent abs.toOrdinaryNDEvent ev.toAnticipatedRNDEventSpec

/-- Variant of `AnticipatedRNDEventSpec` with implicit `Unit` input and output types -/
structure AnticipatedRNDEventSpec'' (v) [Preorder v] (AM) [@Machine ACTX AM] (M) [instM:@Machine CTX M] [Refinement AM M]
  (abs : OrdinaryNDEvent AM Unit Unit)
  extends _Variant v (instM:=instM), RNDEventSpec'' AM M abs where

  nonIncreasing (m : M):
    Machine.invariant m
    → (grd : guard m)
    → ∀ m', effect m grd m'
            → variant m' ≤ variant m

@[simp]
def AnticipatedRNDEventSpec''.toAnticipatedRNDEventSpec [Preorder v] [@Machine ACTX AM] [@Machine CTX M] [Refinement AM M]
  (abs : OrdinaryNDEvent AM Unit Unit)
  (ev : AnticipatedRNDEventSpec'' v AM M abs): AnticipatedRNDEventSpec v AM M (α:=Unit) (β:=Unit) (α':=Unit) (β':=Unit) abs :=
  {
    toRNDEventSpec := ev.toRNDEventSpec
    variant := ev.variant
    nonIncreasing:= fun m x => by simp ; apply ev.nonIncreasing
  }

/-- Variant of `newAnticipatedRNDEventfromOrdinary` with implicit `Unit` input and output types -/
@[simp]
def newAnticipatedRNDEventfromOrdinary'' [Preorder v] [@Machine ACTX AM] [@Machine CTX M] [Refinement AM M]
  (abs : OrdinaryNDEvent AM Unit Unit) (ev : AnticipatedRNDEventSpec'' v AM M abs) : AnticipatedRNDEvent v AM M Unit Unit :=
  _newAnticipatedRNDEvent abs ev.toAnticipatedRNDEventSpec

/-- Variant of `newAnticipatedRNDEventfromAnticipated` with implicit `Unit` input and output types -/
@[simp]
def newAnticipatedRNDEventfromAnticipated'' [Preorder v] [@Machine ACTX AM] [@Machine CTX M] [Refinement AM M]
  (abs : AnticipatedNDEvent v AM Unit Unit) (ev : AnticipatedRNDEventSpec'' v AM M abs.toOrdinaryNDEvent) : AnticipatedRNDEvent v AM M Unit Unit :=
  _newAnticipatedRNDEvent abs.toOrdinaryNDEvent ev.toAnticipatedRNDEventSpec

/-!
## Convergent refined events
-/

/-- Internal representation of proof obligations for convergent refined non-deterministic events -/
structure _ConvergentRNDEventPO (v) [Preorder v] [WellFoundedLT v]  [@Machine ACTX AM] [instM:@Machine CTX M] [instR: Refinement AM M]
  (ev : _NDEvent M α β) (kind : EventKind) (α') (β')
          extends _Variant v (instM:=instM), _AnticipatedRNDEventPO (instR:=instR) v ev kind α' β' where

  convergence (m : M) (x : α):
    Machine.invariant m
    → (grd : ev.guard m x)
    → ∀ y, ∀ m', ev.effect m x grd (y, m')
                → variant m' < variant m

/-- The representation of convergent non-deterministic refined events, constructed
by specifications structures, e.g. `ConvergentRNDEventSpec`,
 and smart constructors, e.g. `newConvergentRNDEvent`. -/
structure ConvergentRNDEvent (v) [Preorder v] [WellFoundedLT v] (AM) [@Machine ACTX AM] (M) [@Machine CTX M] [instR: Refinement AM M]
  (α β) (α':=α) (β':=β)
  extends _NDEvent M α β where
  po : _ConvergentRNDEventPO v (instR:=instR) to_NDEvent (EventKind.TransDet Convergence.Anticipated) α' β'

@[simp]
def ConvergentRNDEvent.toConvergentNDEvent [Preorder v] [WellFoundedLT v] [@Machine ACTX AM] [@Machine CTX M] [instR: Refinement AM M]
  (ev : ConvergentRNDEvent v AM M α β α' β') : ConvergentNDEvent v M α β :=
  { to_NDEvent := ev.to_NDEvent
    po := {
      safety := ev.po.safety
      feasibility := ev.po.feasibility
      variant := ev.po.variant
      nonIncreasing := fun m x => by
        simp
        intros Hinv Hgrd y m' Heff
        have Hcv := ev.po.convergence m x Hinv Hgrd y m' Heff
        exact le_of_lt Hcv

      convergence := ev.po.convergence
    }
  }

/-- Specification of convergent, non-deterministic refined events.
with: `v` a variant type assumed to be pre-ordered with well-founded less-than relation,
 `AM` the abstact machine type, `M` the concrete maching type,
 `α` the concrete input parameter type, `α'` the corresponding abstract input type (by default, `α`)
 `β` the concrete input parameter type, `β'` the corresponding abstract input type (by default, `β`)

The input and output types can be lifted to the abstract, if needed,
 using the `lift_in` and `lift_out` components.

The added proof obligation, beyond `safety` , guard `strengthening`,
abstract event `simulation`, is a `convergence` requirement.
 -/
structure ConvergentRNDEventSpec (v) [Preorder v] [WellFoundedLT v] (AM) [@Machine ACTX AM] (M) [instM:@Machine CTX M] [Refinement AM M]
  {α β α' β'} (abs : OrdinaryNDEvent AM α' β')
  extends _Variant v (instM:=instM), RNDEventSpec AM M (α:=α) (β:=β) (α':=α') (β':=β') abs where

  /-- Proof obligation: the variant strictly decreases. -/
  convergence (m : M) (x : α):
    Machine.invariant m
    → (grd : guard m x)
    → ∀ y, ∀ m', effect m x grd (y, m')
                 → variant m' < variant m

/-- Smart constructor for convergent non-deterministic refined event,
with: `abs` the event to refine, and
  `ev` the refined event specification (cf. `ConvergentRNDEventSpec`).
-/
@[simp]
def newConvergentRNDEvent [Preorder v] [WellFoundedLT v] [@Machine ACTX AM] [@Machine CTX M] [Refinement AM M]
  (abs : OrdinaryNDEvent AM α' β') (ev : ConvergentRNDEventSpec v AM M (α:=α) (β:=β) (α':=α') (β':=β') abs) : ConvergentRNDEvent v AM M α β α' β' :=
  {
    to_NDEvent := ev.to_NDEvent
    po := {
      safety := ev.safety
      feasibility := ev.feasibility
      abstract := abs.to_NDEvent
      strengthening := ev.strengthening
      simulation := ev.simulation
      variant := ev.variant
      nonIncreasing := fun m x => by
        simp
        intros Hinv Hgrd y m' Heff
        have Hcnv := ev.convergence m x Hinv Hgrd y m' Heff
        apply le_of_lt ; assumption
      convergence := ev.convergence
    }
  }

/-- Variant of `ConvergentRNDEventSpec` with implicit `Unit` output type -/
structure ConvergentRNDEventSpec' (v) [Preorder v] [WellFoundedLT v] (AM) [@Machine ACTX AM] (M) [instM:@Machine CTX M] [Refinement AM M]
  {α α'} (abs : OrdinaryNDEvent AM α' Unit)
  extends _Variant v (instM:=instM), RNDEventSpec' AM M (α:=α) (α':=α') abs where

  convergence (m : M) (x : α):
    Machine.invariant m
    → (grd : guard m x)
    → ∀ m', effect m x grd m'
            → variant m' < variant m

@[simp]
def ConvergentRNDEventSpec'.toConvergentRNDEventSpec [Preorder v] [WellFoundedLT v] [@Machine ACTX AM] [@Machine CTX M] [Refinement AM M]
  (abs : OrdinaryNDEvent AM α' Unit)
  (ev : ConvergentRNDEventSpec' v AM M (α:=α) (α':=α') abs): ConvergentRNDEventSpec v AM M (α:=α) (β:=Unit) (α':=α') (β':=Unit) abs :=
  {
    toRNDEventSpec := ev.toRNDEventSpec
    variant := ev.variant
    convergence:= fun m x => by simp ; apply ev.convergence
  }

/-- Variant of `newConvergentRNDEvent` with implicit `Unit` output type -/
@[simp]
def newConvergentRNDEvent' [Preorder v] [WellFoundedLT v] [@Machine ACTX AM] [@Machine CTX M] [Refinement AM M]
  (abs : OrdinaryNDEvent AM α' Unit) (ev : ConvergentRNDEventSpec' v AM M (α:=α) (α':=α') abs) : ConvergentRNDEvent v AM M α Unit α' Unit :=
  newConvergentRNDEvent abs ev.toConvergentRNDEventSpec

/-- Variant of `ConvergentRNDEventSpec` with implicit `Unit` input and output types -/
structure ConvergentRNDEventSpec'' (v) [Preorder v] [WellFoundedLT v] (AM) [@Machine ACTX AM] (M) [instM:@Machine CTX M] [Refinement AM M]
  (abs : OrdinaryNDEvent AM Unit Unit)
  extends _Variant v (instM:=instM), RNDEventSpec'' AM M abs where

  convergence (m : M):
    Machine.invariant m
    → (grd : guard m)
    → ∀ m', effect m grd m'
            → variant m' < variant m

@[simp]
def ConvergentRNDEventSpec''.toConvergentRNDEventSpec [Preorder v] [WellFoundedLT v] [@Machine ACTX AM] [@Machine CTX M] [Refinement AM M]
  (abs : OrdinaryNDEvent AM Unit Unit)
  (ev : ConvergentRNDEventSpec'' v AM M abs): ConvergentRNDEventSpec v AM M (α:=Unit) (β:=Unit) (α':=Unit) (β':=Unit) abs :=
  {
    toRNDEventSpec := ev.toRNDEventSpec
    variant := ev.variant
    convergence:= fun m x => by simp ; apply ev.convergence
  }

/-- Variant of `newConvergentRNDEvent` with implicit `Unit` input and output types -/
@[simp]
def newConvergentRNDEvent'' [Preorder v] [WellFoundedLT v] [@Machine ACTX AM] [@Machine CTX M] [Refinement AM M]
  (abs : OrdinaryNDEvent AM Unit Unit) (ev : ConvergentRNDEventSpec'' v AM M abs) : ConvergentRNDEvent v AM M Unit Unit :=
  newConvergentRNDEvent abs ev.toConvergentRNDEventSpec
