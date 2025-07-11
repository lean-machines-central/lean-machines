
import Mathlib.Order.RelClasses

import LeanMachines.Event.Basic
import LeanMachines.Event.Ordinary


/-!
## Convergent deterministic events

This module defines the user-level API for constructing
and manipulating **convergent** (and anticipated) deterministic events.

Convergent events cannot be enabled infinitely often in isolation.
For this, a further convergence proof obligation is added to
the "ordinary" POs. The ingredients we use are the same as in Event-B:

 1. the introduction of a **variant**, a well-founded ordering relation

 2. a proof that the variant decreases strictly each time the event
 action is "performed".

Alternatively, **anticipated** event are proved only "non-increasing",
which allows to postpone the actual convergence proof to further
refinements of the event.

 We rely on Mathlib's notion of well-founded relations, most notably
 the `Preorder` and `WellFoundedLT` typeclasses from the
 `Order.RelClasses` package of Mathlib.

Basic well-founded orders are proposed, such as the natural ordering for
natural numbers (type `Nat`), or subset ordering for finite sets
 (type `FinSet α`), and so on.  Order composition means are also
 available, such as lexicographic product ordering, multiset ordering, etc.
 And of course, custom orderings can be defined (cf. Mathlib's documentation).

-/

/-- The definition of a `variant` of type `v` obtained from
a machine pre-state. The type `v` must be a preorder
(i.e. an instance of the `Preorder` typeclass). -/
structure _Variant (v) [Preorder v] [instM:Machine CTX M] where
  variant : M → v

/-!
### Anticipated events
-/

/-- The internal representation of proof obligations for anticipated events. -/
structure _AnticipatedEventPO (v) [Preorder v] [instM: Machine CTX M] (ev : _Event M α β) (kind : EventKind)
          extends _Variant v (instM:=instM), _EventPO ev kind  where

  nonIncreasing (m : M) (x : α):
    Machine.invariant m
    → (grd : ev.guard m x)
    → let (_, m') := ev.action m x grd
      variant m' ≤ variant m

/-- The type of deterministic anticipated events.
It is an event for machine type `M` with input type `α` and output type `β`.
The non-increasing argument is based on the variant type `v` assumed
to be a preorder. -/
structure AnticipatedEvent (v) [Preorder v] (M) [Machine CTX M] (α) (β)
          extends (_Event M α β)  where
  po : _AnticipatedEventPO v to_Event (EventKind.TransDet Convergence.Anticipated)

@[simp]
private def AnticipatedEvent_fromOrdinary {v} [Preorder v] {M} [Machine CTX M] (ev : OrdinaryEvent M α β)
  (variant : M → v)
  (Hnincr: ∀ (m : M) (x : α),
    Machine.invariant m
    → (grd : ev.guard m x)
    → let (_, m') := ev.action m x grd
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

/-- The "downgrading" of an anticipated event to an ordinary one. -/
@[simp]
def AnticipatedEvent.toOrdinaryEvent [Preorder v] [Machine CTX M]
  (ev : AnticipatedEvent v M α β) : OrdinaryEvent M α β :=
  {
    to_Event := ev.to_Event
    po := {
      safety := ev.po.safety
    }
  }

axiom AnticipatedEvent.ext [Preorder v]{CTX} {M} [Machine CTX M] {α β}
  (ev₁ ev₂: AnticipatedEvent v M α β):
  ev₁.toOrdinaryEvent = ev₂.toOrdinaryEvent
  → ev₁.po.variant = ev₂.po.variant
  → ev₁ = ev₂

-- theorem AnticipatedEvent.ext [Preorder v] [WellFoundedLT v] {CTX} {M} [Machine CTX M] {α β}
--   (ev₁ ev₂: AnticipatedEvent v M α β):
--   ev₁.toOrdinaryEvent = ev₂.toOrdinaryEvent
--   → ev₁.po.variant = ev₂.po.variant
--   → ev₁ = ev₂ :=
--   by
--     intros Heq Hvar

--     have ⟨to_event₁,to_variant₁,to_ev_po₁,ni₁⟩ := ev₁
--     have ⟨to_event₂,to_variant₂,to_ev_po₂,ni₂⟩ := ev₂
--     simp at Hvar
--     simp at Heq

--     have h₁ : ni₁ =
--       by
--         rw[Heq]
--         rw[Hvar]
--         exact ni₂
--          :=
--     by
--       simp
--     rw[h₁]

--     have h₂ : to_ev_po₁ =
--       by
--         rw[Heq]
--         exact to_ev_po₂
--       := by simp

--     rw[h₂]
--     simp
--     constructor
--     · exact Heq
--     have h : to_variant₁ = to_variant₂ := by sorry


--     sorry

/-- The specification of a deterministic, anticipated event for machine `M`
with input type `α` and output type `β`. The non-increasing proof relies
 on a variant type `v` assumed to be a preorder.
Note that the guard, action and safety PO of the event must be also
specified, as in the ordinary case (cf. `OrdinaryEventSpec`).
  -/
structure AnticipatedEventSpec (v) [Preorder v] {CTX} (M) [instM: Machine CTX M] (α) (β)
  extends _Variant v (instM:=instM), EventSpec M α β where
  /-- Proof obligation: the variant is non-increasing. -/
  nonIncreasing (m : M) (x : α):
    Machine.invariant m
    → (grd : guard m x)
    → let m' := (action m x grd).2
      variant m' ≤ variant m

/-- Construction of an anticipated deterministic event from a
`AnticipatedEventSpec` specification. -/
@[simp]
def newAnticipatedEvent {v} [Preorder v] {M} [Machine CTX M] (ev : AnticipatedEventSpec v M α β) : AnticipatedEvent v M α β :=
  AnticipatedEvent_fromOrdinary (newEvent ev.toEventSpec) ev.to_Variant.variant ev.nonIncreasing

/-- Variant of `AnticipatedEventSpec` with implicit `Unit` output type -/
structure AnticipatedEventSpec' (v) [Preorder v] (M) [instM:Machine CTX M] (α)
  extends _Variant v (instM:=instM), EventSpec' M α where

  nonIncreasing (m : M) (x : α):
    Machine.invariant m
    → (grd : guard m x)
    → let m' := (action m x grd)
      variant m' ≤ variant m

@[simp]
def AnticipatedEventSpec'.toAnticipatedEventSpec {v} [Preorder v] {M} [Machine CTX M] (ev : AnticipatedEventSpec' v M α) : AnticipatedEventSpec v M α Unit :=
  {
    toEventSpec := ev.toEventSpec
    variant := ev.variant
    nonIncreasing := ev.nonIncreasing
  }

/-- Variant of `newAnticipatedEvent` with implicit `Unit` output type -/
@[simp]
def newAnticipatedEvent' {v} [Preorder v] {M} [Machine CTX M] (ev : AnticipatedEventSpec' v M α ) : AnticipatedEvent v M α Unit :=
  newAnticipatedEvent ev.toAnticipatedEventSpec

/-- Variant of `AnticipatedEventSpec` with implicit `Unit` input and output types -/
structure AnticipatedEventSpec'' (v) [Preorder v] (M) [instM:Machine CTX M]
  extends _Variant v (instM:=instM), EventSpec'' M where

  nonIncreasing (m : M):
    Machine.invariant m
    → (grd : guard m)
    → let m' := (action m grd)
      variant m' ≤ variant m

@[simp]
def AnticipatedEventSpec''.toAnticipatedEventSpec {v} [Preorder v] {M} [Machine CTX M] (ev : AnticipatedEventSpec'' v M) : AnticipatedEventSpec v M Unit Unit :=
  {
    toEventSpec := ev.toEventSpec
    variant := ev.variant
    nonIncreasing := fun m () => by apply ev.nonIncreasing
  }

/-- Variant of `newAnticipatedEvent` with implicit `Unit` input and output types -/
@[simp]
def newAnticipatedEvent'' {v} [Preorder v] {M} [Machine CTX M] (ev : AnticipatedEventSpec'' v M) : AnticipatedEvent v M Unit Unit :=
  newAnticipatedEvent ev.toAnticipatedEventSpec


/-!
### Convergent events
-/

/-- The internal representation of proof obligations for convergent events. -/
structure _ConvergentEventPO (v) [Preorder v] [WellFoundedLT v] [Machine CTX M] (ev : _Event M α β) (kind : EventKind)
          extends _AnticipatedEventPO v ev kind  where

  convergence (m : M) (x : α):
    Machine.invariant m
    → (grd : ev.guard m x)
    → let (_, m') := ev.action m x grd
      variant m' < variant m

/-- The type of deterministic convergent events.
It is an event for machine type `M` with input type `α` and output type `β`.
The convergence argument is based on the variant type `v` assumed
to be a well-founded preorder. -/
structure ConvergentEvent (v) [Preorder v]  [WellFoundedLT v] (M) [Machine CTX M] (α) (β)
          extends (_Event M α β)  where
  po : _ConvergentEventPO v to_Event (EventKind.TransDet Convergence.Convergent)

@[simp]
private def ConvergentEvent_fromOrdinary  {v} [Preorder v] [WellFoundedLT v] {M} [Machine CTX M] (ev : OrdinaryEvent M α β)
  (variant : M → v)
  (Hconv: ∀ (m : M) (x : α),
    Machine.invariant m
    → (grd : ev.guard m x)
    → let m' := (ev.action m x grd).2
      variant m' < variant m)
 : ConvergentEvent v M α β :=
 {
  guard := ev.guard
  action := ev.action
  po := {
    safety := ev.po.safety
    variant := variant
    nonIncreasing := fun m x => by
      simp
      intros Hinv Hgrd
      have Hconv' := Hconv m x Hinv Hgrd
      apply le_of_lt
      exact Hconv'
    convergence := Hconv
  }
 }

@[simp]
def ConvergentEvent.toOrdinaryEvent [Preorder v] [WellFoundedLT v] [Machine CTX M]
  (ev : ConvergentEvent v M α β) : OrdinaryEvent M α β :=
  {
    to_Event := ev.to_Event
    po := {
      safety := ev.po.safety
    }
  }

/-- The "downgrading" of a convergent event to an anticipated one. -/
@[simp]
def ConvergentEvent.toAnticipatedEvent [Preorder v] [WellFoundedLT v] [Machine CTX M]
  (ev : ConvergentEvent v M α β) : AnticipatedEvent v M α β :=
  {
    to_Event := ev.to_Event
    po := {
      safety := ev.po.safety
      variant := ev.po.variant
      nonIncreasing := ev.po.nonIncreasing
    }
  }


/-- The specification of a deterministic, convergent event for machine `M`
with input type `α` and output type `β`. The convergence proof relies
 on a variant type `v` assumed to be a well-founded preorder.
Note that the guard, action and safety PO of the event must be also
specified, as in the ordinary case (cf. `OrdinaryEventSpec`).
  -/
structure ConvergentEventSpec (v) [Preorder v] [WellFoundedLT v] (M) [instM:Machine CTX M] (α) (β)
  extends _Variant v (instM:=instM), EventSpec M α β where
  /-- Proof obligation: the variant is strictly decreasing. -/
  convergence (m : M) (x : α):
    Machine.invariant m
    → (grd : guard m x)
    → let m' := (action m x grd).2
      variant m' < variant m

/-- Construction of a convergent deterministic event from a
`ConvergentEventSpec` specification. -/
@[simp]
def newConvergentEvent {v} [Preorder v] [WellFoundedLT v] {M} [Machine CTX M] (ev : ConvergentEventSpec v M α β) : ConvergentEvent v M α β :=
  ConvergentEvent_fromOrdinary (newEvent ev.toEventSpec) ev.to_Variant.variant ev.convergence

@[simp]
private def ConvergentEvent_fromAnticipated {v} [Preorder v] [WellFoundedLT v] {M} [Machine CTX M] (ev : AnticipatedEvent v M α β)
    (hconv : (m : M) → (x : α)
    → Machine.invariant m
    → (grd : ev.guard m x)
    → let m' := (ev.action m x grd).2
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


axiom ConvergentEvent.ext [Preorder v] [WellFoundedLT v] {CTX} {M} [Machine CTX M] {α β} (ev₁ ev₂: ConvergentEvent v M α β):
  ev₁.toOrdinaryEvent = ev₂.toOrdinaryEvent
  → ev₁.po.variant = ev₂.po.variant
  → ev₁ = ev₂



/-- Variant of `ConvergentEventSpec` with implicit `Unit` output type -/
structure ConvergentEventSpec' (v) [Preorder v] [WellFoundedLT v] (M) [instM:Machine CTX M] (α)
  extends _Variant v (instM:=instM), EventSpec' M α where

  convergence (m : M) (x : α):
    Machine.invariant m
    → (grd : guard m x)
    → let m' := (action m x grd)
      variant m' < variant m

@[simp]
def ConvergentEventSpec'.toConvergentEventSpec {v} [Preorder v] [WellFoundedLT v] {M} [Machine CTX M] (ev : ConvergentEventSpec' v M α) : ConvergentEventSpec v M α Unit :=
  {
    toEventSpec := ev.toEventSpec
    variant := ev.variant
    convergence := ev.convergence
  }

/-- Variant of `newConvergentEvent` with implicit `Unit` output type -/
@[simp]
def newConvergentEvent' {v} [Preorder v] [WellFoundedLT v] {M} [Machine CTX M] (ev : ConvergentEventSpec' v M α ) : ConvergentEvent v M α Unit :=
  newConvergentEvent ev.toConvergentEventSpec

/-- Variant of `ConvergentEventSpec` with implicit `Unit` input and output types -/
structure ConvergentEventSpec'' (v) [Preorder v] [WellFoundedLT v] (M) [instM:Machine CTX M]
  extends _Variant v (instM:=instM), EventSpec'' M where

  convergence (m : M):
    Machine.invariant m
    → (grd : guard m)
    → let m' := (action m grd)
      variant m' < variant m

@[simp]
def ConvergentEventSpec''.toConvergentEventSpec {v} [Preorder v] [WellFoundedLT v] {M} [Machine CTX M] (ev : ConvergentEventSpec'' v M) : ConvergentEventSpec v M Unit Unit :=
  {
    toEventSpec := ev.toEventSpec
    variant := ev.variant
    convergence := fun m () => by apply ev.convergence
  }

/-- Variant of `newConvergentEvent` with implicit `Unit` input and output types -/
@[simp]
def newConvergentEvent'' {v} [Preorder v] [WellFoundedLT v] {M} [Machine CTX M] (ev : ConvergentEventSpec'' v M) : ConvergentEvent v M Unit Unit :=
  newConvergentEvent ev.toConvergentEventSpec
