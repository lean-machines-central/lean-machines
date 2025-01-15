
import LeanMachines.Refinement.Relational.Basic
import LeanMachines.Event.Convergent

/-!

## Convergent refined events

This module defines the construction of anticipated and
convergent events.

This builds on the well-founded ordering relations of Mathlib4,
 which means convergence is not restricted to e.g. natural number
 of finite set orderings (cf. module `Event.Convergent`).

-/

open Refinement

/-!
### Anticipated refined events
-/

/-- Internal representation of proof obligations for anticipated events -/
structure _AnticipatedREventPO (v) [Preorder v]  [Machine ACTX AM] [instM:Machine CTX M] [instR: Refinement AM M]
  (ev : _Event M α β) (kind : EventKind) (α') (β')
          extends _Variant v (instM:=instM), _REventPO (instR:=instR) ev kind α' β'  where

  nonIncreasing (m : M) (x : α):
    Machine.invariant m
    → (grd : ev.guard m x)
    → let (_, m') := ev.action m x grd
      variant m' ≤ variant m

/-- The representation of anticipated refined events, constructed
by specifications structures, e.g. `AnticipatedREventSpec`,
 and smart constructors, e.g. `newAnticipatedREvent`. -/
structure AnticipatedREvent (v) [Preorder v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: Refinement AM M]
  (α β) (α':=α) (β':=β)
  extends _Event M α β where
  po : _AnticipatedREventPO v (instR:=instR) to_Event (EventKind.TransDet Convergence.Anticipated) α' β'

@[simp]
def AnticipatedREvent.toAnticipatedEvent [Preorder v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (ev : AnticipatedREvent v AM M α β α' β') : AnticipatedEvent v M α β :=
  { to_Event := ev.to_Event
    po := {
      to_EventPO := ev.po.to_EventPO
      variant := ev.po.variant
      nonIncreasing := ev.po.nonIncreasing
    } }

/-- Specification of anticipated refined events.
with: `v` a variant type assumed to be pre-ordered,
 `AM` the abstact machine type, `M` the concrete maching type,
 `α` the concrete input parameter type, `α'` the corresponding abstract input type (by default, `α`)
 `β` the concrete input parameter type, `β'` the corresponding abstract input type (by default, `β`)
The `abs` parameter is the ordinary event intended to be refined.

Note that `abs` should be, in practice, either an ordinary event or an anticipated one.
An abstract convergent event should be refined as a convergent event.

The input and output types can be lifted to the abstract, if needed,
 using the `lift_in` and `lift_out` components.

The added proof obligation, beyond `safety` , guard `strengthening`,
abstract event `simulation`, is a `nonIncreasing` requirement.
 -/
structure AnticipatedREventSpec (v) [Preorder v] (AM) [Machine ACTX AM] (M) [instM:Machine CTX M] [Refinement AM M]
  {α β α' β'} (abs : OrdinaryEvent AM α' β')
  extends _Variant v (instM:=instM), REventSpec AM M (α:=α) (β:=β) (α':=α') (β':=β') abs where

  /-- Proof obligation: the variant does not increases. -/
  nonIncreasing (m : M) (x : α):
    Machine.invariant m
    → (grd : guard m x)
    → let m' := (action m x grd).2
      variant m' ≤ variant m

@[simp]
private def _newAnticipatedREvent [Preorder v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : OrdinaryEvent AM α' β') (ev : AnticipatedREventSpec v AM M (α:=α) (β:=β) (α':=α') (β':=β') abs) : AnticipatedREvent v AM M α β α' β' :=
  {
    to_Event := ev.to_Event
    po := {
      safety := ev.safety
      lift_in := ev.lift_in
      lift_out := ev.lift_out
      abstract := abs.to_Event
      strengthening := ev.strengthening
      simulation := ev.simulation
      variant := ev.variant
      nonIncreasing := ev.nonIncreasing
    }
  }

/-- Smart constructor for anticipated refined event,
with: `abs` the ordinary event to refine, and
  `ev` the refined event specification
  (cf. `AnticipatedREventSpec`).
-/
@[simp]
def newAnticipatedREventfromOrdinary [Preorder v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : OrdinaryEvent AM α' β') (ev : AnticipatedREventSpec v AM M (α:=α) (β:=β) (α':=α') (β':=β') abs) : AnticipatedREvent v AM M α β α' β' :=
  _newAnticipatedREvent abs ev

/-- Smart constructor for anticipated refined event,
with: `abs` the anticipated event to refine, and
  `ev` the refined event specification
  (cf. `AnticipatedREventSpec`).

-/
@[simp]
def newAnticipatedREventfromAnticipated [Preorder v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : AnticipatedEvent v AM α' β') (ev : AnticipatedREventSpec v AM M (α:=α) (β:=β) (α':=α') (β':=β') abs.toOrdinaryEvent) : AnticipatedREvent v AM M α β α' β' :=
  _newAnticipatedREvent abs.toOrdinaryEvent ev

/-- Variant of `AnticipatedREventSpec` with implicit `Unit` output type -/
structure AnticipatedREventSpec' (v) [Preorder v] (AM) [Machine ACTX AM] (M) [instM:Machine CTX M] [Refinement AM M]
  {α α'} (abs : OrdinaryEvent AM α' Unit)
  extends _Variant v (instM:=instM), REventSpec' AM M (α:=α) (α':=α') abs where

  nonIncreasing (m : M) (x : α):
    Machine.invariant m
    → (grd : guard m x)
    → let m' := action m x grd
      variant m' ≤ variant m

@[simp]
def AnticipatedREventSpec'.toAnticipatedREventSpec [Preorder v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : OrdinaryEvent AM α' Unit) (ev : AnticipatedREventSpec' v AM M (α:=α) (α':=α') abs) : AnticipatedREventSpec v AM M (α:=α) (β:=Unit) (α':=α') (β':=Unit) abs :=
  {
    toREventSpec := ev.toREventSpec abs
    variant := ev.variant
    nonIncreasing := ev.nonIncreasing
  }

@[simp]
private def _newAnticipatedREvent' [Preorder v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : OrdinaryEvent AM α' Unit) (ev : AnticipatedREventSpec' v AM M (α:=α) (α':=α') abs) : AnticipatedREvent v AM M α Unit α' Unit :=
  _newAnticipatedREvent abs ev.toAnticipatedREventSpec

/-- Variant of `newAnticipatedREventFromOrdinary` with implicit `Unit` output type -/
@[simp]
def newAnticipatedREventfromOrdinary' [Preorder v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : OrdinaryEvent AM α' Unit) (ev : AnticipatedREventSpec' v AM M (α:=α) (α':=α') abs) : AnticipatedREvent v AM M α Unit α' Unit :=
  _newAnticipatedREvent' abs ev

/-- Variant of `newAnticipatedREventFromAnticipated` with implicit `Unit` output type -/
@[simp]
def newAnticipatedREventfromAnticipated' [Preorder v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : AnticipatedEvent v AM α' Unit) (ev : AnticipatedREventSpec' v AM M (α:=α) (α':=α') abs.toOrdinaryEvent) : AnticipatedREvent v AM M α Unit α' Unit :=
  _newAnticipatedREvent' abs.toOrdinaryEvent ev

/-- Variant of `AnticipatedREventSpec` with implicit `Unit` input and output types -/
structure AnticipatedREventSpec'' (v) [Preorder v] (AM) [Machine ACTX AM] (M) [instM:Machine CTX M] [Refinement AM M]
  (abs : OrdinaryEvent AM Unit Unit)
  extends _Variant v (instM:=instM), REventSpec'' AM M abs where

  nonIncreasing (m : M):
    Machine.invariant m
    → (grd : guard m)
    → let m' := action m grd
      variant m' ≤ variant m

@[simp]
def AnticipatedREventSpec''.toAnticipatedREventSpec [Preorder v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : OrdinaryEvent AM Unit Unit) (ev : AnticipatedREventSpec'' v AM M abs) : AnticipatedREventSpec v AM M (α:=Unit) (β:=Unit) (α':=Unit) (β':=Unit) abs :=
  {
    toREventSpec := ev.toREventSpec abs
    variant := ev.variant
    nonIncreasing := fun m grd => by simp ; apply ev.nonIncreasing
  }

@[simp]
private def _newAnticipatedREvent'' [Preorder v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : OrdinaryEvent AM Unit Unit) (ev : AnticipatedREventSpec'' v AM M abs) : AnticipatedREvent v AM M Unit Unit :=
  _newAnticipatedREvent abs ev.toAnticipatedREventSpec

/-- Variant of `newAnticipatedREventfromOrdinary` with implicit `Unit` input and output types -/
@[simp]
def newAnticipatedREventfromOrdinary'' [Preorder v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : OrdinaryEvent AM Unit Unit) (ev : AnticipatedREventSpec'' v AM M abs) : AnticipatedREvent v AM M Unit Unit :=
  _newAnticipatedREvent'' abs ev

/-- Variant of `newAnticipatedREventfromAnticipated` with implicit `Unit` input and output types -/
@[simp]
def newAnticipatedREventfromAnticipated'' [Preorder v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : AnticipatedEvent v AM Unit Unit) (ev : AnticipatedREventSpec'' v AM M abs.toOrdinaryEvent) : AnticipatedREvent v AM M Unit Unit :=
  _newAnticipatedREvent'' abs.toOrdinaryEvent ev

/-!
### Convergent refined events
-/

/-- Internal representation of proof obligations for convergent refined events -/
structure _ConvergentREventPO (v) [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [instR: Refinement AM M]
  (ev : _Event M α β) (kind : EventKind) (α') (β')
  extends _AnticipatedREventPO (instR:=instR) v ev kind α' β' where

  convergence (m : M) (x : α):
    Machine.invariant m
    → (grd : ev.guard m x)
    → let (_, m') := ev.action m x grd
      variant m' < variant m

/-- The representation of convergent refined events, constructed
by specifications structures, e.g. `ConvergentREventSpec`,
 and smart constructors, e.g. `newConvergentREvent`. -/
structure ConvergentREvent (v) [Preorder v] [WellFoundedLT v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: Refinement AM M]
  (α β) (α':=α) (β':=β)
  extends _Event M α β where
  po : _ConvergentREventPO v (instR:=instR) to_Event (EventKind.TransDet Convergence.Convergent) α' β'

@[simp]
def ConvergentREvent.toConvergentEvent [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (ev : ConvergentREvent v AM M α β α' β') : ConvergentEvent v M α β :=
  { to_Event := ev.to_Event
    po := {
      safety := ev.po.safety
      variant := ev.po.variant
      nonIncreasing := ev.po.nonIncreasing
      convergence := ev.po.convergence
    }
  }

/-- Specification of convergent refined events.
with: `v` a variant type assumed to be pre-ordered with well-founded less-than relation,
 `AM` the abstact machine type, `M` the concrete maching type,
 `α` the concrete input parameter type, `α'` the corresponding abstract input type (by default, `α`)
 `β` the concrete input parameter type, `β'` the corresponding abstract input type (by default, `β`)

The input and output types can be lifted to the abstract, if needed,
 using the `lift_in` and `lift_out` components.

The added proof obligation, beyond `safety` , guard `strengthening`,
abstract event `simulation`, is a `convergence` requirement.
 -/
structure ConvergentREventSpec (v) [Preorder v] [WellFoundedLT v] (AM) [Machine ACTX AM] (M) [instM:Machine CTX M] [Refinement AM M]
  {α β α' β'} (abs : OrdinaryEvent AM α' β')
  extends _Variant v (instM:=instM), REventSpec AM M (α:=α) (β:=β) (α':=α') (β':=β') abs where

  /-- Proof obligation: the variant strictly decreases. -/
  convergence (m : M) (x : α):
    Machine.invariant m
    → (grd : guard m x)
    → let m' := (action m x grd).2
      variant m' < variant m

/-- Smart constructor for convergent refined event,
with: `abs` the event to refine, and
  `ev` the refined event specification (cf. `ConvergentREventSpec`).
-/
@[simp]
def newConvergentREvent [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : OrdinaryEvent AM α' β') (ev : ConvergentREventSpec v AM M (α:=α) (β:=β) (α':=α') (β':=β') abs) : ConvergentREvent v AM M α β α' β':=
  {
    guard := ev.guard
    action := ev.action
    po := {
      safety := ev.safety
      lift_in := ev.lift_in
      lift_out := ev.lift_out
      abstract := abs.to_Event
      strengthening := ev.strengthening
      simulation := ev.simulation
      variant := ev.variant
      nonIncreasing := fun m x => by
        simp
        intros Hinv Hgrd
        have Hcnv := ev.convergence m x Hinv Hgrd
        simp at Hcnv
        apply le_of_lt ; assumption
      convergence := ev.convergence
    }
  }

/-- Variant of `ConvergentREventSpec` with implicit `Unit` output type -/
structure ConvergentREventSpec' (v) [Preorder v] [WellFoundedLT v] (AM) [Machine ACTX AM] (M) [instM:Machine CTX M] [Refinement AM M]
  {α α'} (abs : OrdinaryEvent AM α' Unit)
  extends _Variant v (instM:=instM), REventSpec' AM M (α:=α) (α':=α') abs where

  convergence (m : M) (x : α):
    Machine.invariant m
    → (grd : guard m x)
    → let m' := action m x grd
      variant m' < variant m

@[simp]
def ConvergentREventSpec'.toConvergentREventSpec [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : OrdinaryEvent AM α' Unit) (ev : ConvergentREventSpec' v AM M (α:=α) (α':=α') abs) : ConvergentREventSpec v AM M (α:=α) (β:=Unit) (α':=α') (β':=Unit) abs :=
  {
    toREventSpec := ev.toREventSpec abs
    variant := ev.variant
    convergence := ev.convergence
  }

/-- Variant of `newConvergentREvent` with implicit `Unit` output type -/
@[simp]
def newConvergentREvent' [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : OrdinaryEvent AM α' Unit) (ev : ConvergentREventSpec' v AM M (α:=α) (α':=α') abs) : ConvergentREvent v AM M α Unit α' Unit :=
  newConvergentREvent abs ev.toConvergentREventSpec

/-- Variant of `ConvergentREventSpec` with implicit `Unit` input and output types -/
structure ConvergentREventSpec'' (v) [Preorder v] [WellFoundedLT v] (AM) [Machine ACTX AM] (M) [instM:Machine CTX M] [Refinement AM M]
  (abs : OrdinaryEvent AM Unit Unit)
  extends _Variant v (instM:=instM), REventSpec'' AM M abs where

  convergence (m : M):
    Machine.invariant m
    → (grd : guard m)
    → let m' := action m grd
      variant m' < variant m

@[simp]
def ConvergentREventSpec''.toConvergentREventSpec [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : OrdinaryEvent AM Unit Unit) (ev : ConvergentREventSpec'' v AM M abs) : ConvergentREventSpec v AM M (α:=Unit) (β:=Unit) (α':=Unit) (β':=Unit) abs :=
  {
    toREventSpec := ev.toREventSpec abs
    variant := ev.variant
    convergence := fun m () => ev.convergence m
  }

/-- Variant of `newConvergentREvent` with implicit `Unit` input and output types -/
@[simp]
def newConvergentREvent'' [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
  (abs : OrdinaryEvent AM Unit Unit) (ev : ConvergentREventSpec'' v AM M abs) : ConvergentREvent v AM M Unit Unit :=
  newConvergentREvent abs ev.toConvergentREventSpec
