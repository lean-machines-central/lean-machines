
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
 available, such as lexicographic produc ordering, multiset ordering, etc.
 And of course, custom orderings can be defined (cf. Mathlib's documentation).

-/

/-- The definition of a `variant` of type `v` obtained from
a machine pre-state. The type `v` must be a preorder
(i.e. an instance of the `Preorder` typeclass). -/
structure _Variant (v) [Preorder v] [Machine CTX M] where
  variant : M → v

/-!
### Anticipated events
-/

/-- The internal representation of proof obligations for anticipated events. -/
structure _AnticipatedEventPO (v) [Preorder v] [Machine CTX M] (ev : _Event M α β) (kind : EventKind)
          extends _Variant v, _EventPO ev kind  where

  nonIncreasing (m : M) (x : α):
    Machine.invariant m
    → ev.guard m x
    → let (_, m') := ev.action m x
      variant m' ≤ variant m

/-- Type type of deterministic anticipated events.
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

/-- The specification of a deterministic, anticipated event for machine `M`
with input type `α` and output type `β`. The non-increasing proof relies
 on a variant type `v` assumed to be a preorder.
Note that the guard, action and safety PO of the event must be also
specified, as in the ordinary case (cf. `OrdinaryEventSpec`).
  -/
structure AnticipatedEventSpec (v) [Preorder v] {CTX} (M) [Machine CTX M] (α) (β)
  extends _Variant v, EventSpec M α β where
  /-- Proof obligation: the variant is non-increasing. -/
  nonIncreasing (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → let m' := (action m x).2
      variant m' ≤ variant m

/-- Construction of an anticipated deterministic event from a
`AnticipatedEventSpec` specification. -/
@[simp]
def newAnticipatedEvent {v} [Preorder v] {M} [Machine CTX M] (ev : AnticipatedEventSpec v M α β) : AnticipatedEvent v M α β :=
  AnticipatedEvent_fromOrdinary (newEvent ev.toEventSpec) ev.to_Variant.variant ev.nonIncreasing

/-- Variant of `AnticipatedEventSpec` with implicit `Unit` output type -/
structure AnticipatedEventSpec' (v) [Preorder v] (M) [Machine CTX M] (α)
  extends _Variant v, EventSpec' M α where

  nonIncreasing (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → let m' := (action m x)
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
structure AnticipatedEventSpec'' (v) [Preorder v] (M) [Machine CTX M]
  extends _Variant v, EventSpec'' M where

  nonIncreasing (m : M):
    Machine.invariant m
    → guard m
    → let m' := (action m)
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
    → ev.guard m x
    → let (_, m') := ev.action m x
      variant m' < variant m

/-- Type type of deterministic convergent events.
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
structure ConvergentEventSpec (v) [Preorder v] [WellFoundedLT v] (M) [Machine CTX M] (α) (β)
  extends _Variant v, EventSpec M α β where
  /-- Proof obligation: the variant is strictly decreasing. -/
  convergence (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → let m' := (action m x).2
      variant m' < variant m

/-- Construction of a convergent deterministic event from a
`ConvergentEventSpec` specification. -/
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

/-- Variant of `ConvergentEventSpec` with implicit `Unit` output type -/
structure ConvergentEventSpec' (v) [Preorder v] [WellFoundedLT v] (M) [Machine CTX M] (α)
  extends _Variant v, EventSpec' M α where

  convergence (m : M) (x : α):
    Machine.invariant m
    → guard m x
    → let m' := (action m x)
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
structure ConvergentEventSpec'' (v) [Preorder v] [WellFoundedLT v] (M) [Machine CTX M]
  extends _Variant v, EventSpec'' M where

  convergence (m : M):
    Machine.invariant m
    → guard m
    → let m' := (action m)
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

/-!
## Algebraic properties of events

The following instantiate various algebraic structures for anticipated
and convergent events (experimental, not documented).

-/

@[simp]
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

/- Contravariant functor -/

abbrev CoAnticipatedEvent (v) [Preorder v] (M) [Machine CTX M] (α) (β) :=
   AnticipatedEvent v M β α

@[simp]
def AnticipatedEvent_from_CoAnticipatedEvent [Preorder v] [Machine CTX M] (ev : CoAnticipatedEvent v M α β) : AnticipatedEvent v M β α := ev

@[simp]
def CoAnticipatedEvent_from_AnticipatedEvent [Preorder v] [Machine CTX M] (ev : AnticipatedEvent v M α β) : CoAnticipatedEvent v M β α := ev

instance [Preorder v] [Machine CTX M]: ContravariantFunctor (CoAnticipatedEvent v M γ) where
  contramap {α β} (f : β → α) (ev : CoAnticipatedEvent v M γ α) :=
  let event := let ev' := coEvent_from_Event ev.to_Event
             let ev'' := ContravariantFunctor.contramap f ev'
             Event_from_CoEvent ev''
  {
    guard := event.guard
    action := event.action
    po := {
      safety := fun m x => by simp [ContravariantFunctor.contramap]
                              intros Hinv Hgrd
                              exact ev.po.safety m (f x) Hinv Hgrd
      variant := ev.po.variant
      nonIncreasing := fun m x => by simp
                                     intros Hinv Hgrd
                                     apply ev.po.nonIncreasing <;> assumption
    }
  }

instance [Preorder v] [Machine CTX M] : LawfullContravariantFunctor (CoAnticipatedEvent v M α) where
  cmap_id _ := by rfl
  cmap_comp _ _ := by rfl

abbrev CoConvergentEvent (v) [Preorder v] [WellFoundedLT v] (M) [Machine CTX M] (α) (β) :=
   ConvergentEvent v M β α

@[simp]
def ConvergentEvent_from_CoConvergentEvent [Preorder v] [WellFoundedLT v] [Machine CTX M] (ev : CoConvergentEvent v M α β) : ConvergentEvent v M β α := ev

@[simp]
def CoConvergentEvent_from_ConvergentEvent [Preorder v] [WellFoundedLT v] [Machine CTX M] (ev : ConvergentEvent v M α β) : CoConvergentEvent v M β α := ev

instance [Preorder v] [WellFoundedLT v] [Machine CTX M]: ContravariantFunctor (CoConvergentEvent v M γ) where
  contramap {α β} (f : β → α) (ev : CoConvergentEvent v M γ α) :=
  let event := let ev' := coEvent_from_Event ev.to_Event
             let ev'' := ContravariantFunctor.contramap f ev'
             Event_from_CoEvent ev''
  {
    guard := event.guard
    action := event.action
    po := {
      safety := fun m x => by simp [ContravariantFunctor.contramap]
                              intros Hinv Hgrd
                              exact ev.po.safety m (f x) Hinv Hgrd
      variant := ev.po.variant
      nonIncreasing := fun m x => by simp
                                     intros Hinv Hgrd
                                     apply ev.po.nonIncreasing <;> assumption
      convergence := fun m x => by simp
                                   intros Hinv Hgrd
                                   apply ev.po.convergence <;> assumption
    }
  }

instance [Preorder v] [WellFoundedLT v] [Machine CTX M] : LawfullContravariantFunctor (CoConvergentEvent v M α) where
  cmap_id _ := by rfl
  cmap_comp _ _ := by rfl

/- Profunctor -/

instance [Preorder v] [Machine CTX M] : Profunctor (AnticipatedEvent v M) where
  dimap {α β} {γ δ} (f : β → α) (g : γ → δ) (ev : AnticipatedEvent v M α γ) : AnticipatedEvent v M β δ :=
    let event := Profunctor.dimap f g ev.to_Event
    {
      guard := fun m x => ev.guard m (f x)
      action := fun m x => event.action m x
      po := {
        safety := fun m x => by simp [Profunctor.dimap]
                                intros Hinv Hgrd
                                let ev' := AnticipatedEvent_from_CoAnticipatedEvent (ContravariantFunctor.contramap f (CoAnticipatedEvent_from_AnticipatedEvent ev))
                                let ev'' := g <$> ev'
                                have Hsafe := ev''.po.safety m x Hinv
                                revert Hsafe ev' ev'' ; simp
                                intro Hsafe
                                exact Hsafe Hgrd

        variant := ev.po.variant

        nonIncreasing := fun m x => by simp
                                       intros Hinv Hgrd
                                       let ev' := AnticipatedEvent_from_CoAnticipatedEvent (ContravariantFunctor.contramap f (CoAnticipatedEvent_from_AnticipatedEvent ev))
                                       let ev'' := g <$> ev'
                                       have Hni := ev''.po.nonIncreasing m x Hinv
                                       revert Hni ev' ev'' ; simp [Functor.map, ContravariantFunctor.contramap]
                                       intro Hni
                                       apply Hni ; exact Hgrd
      }
    }

instance [Preorder v] [Machine CTX M] : LawfulProfunctor (AnticipatedEvent v M) where
  dimap_id := rfl
  dimap_comp _ _ _ _ := rfl

instance [Preorder v] [Machine CTX M] : StrongProfunctor (AnticipatedEvent v M) where
  first' {α β γ} (ev : AnticipatedEvent v M α β): AnticipatedEvent v M (α × γ) (β × γ) :=
    let event := StrongProfunctor.first' ev.to_Event
    {
      guard := fun m (x, y) => ev.guard m x ∧ event.guard m (x, y)
      action := event.action
      po := {
        safety := fun m x => by simp
                                intros Hinv _
                                apply ev.po.safety ; assumption

        variant := ev.po.variant

        nonIncreasing := fun m (x,y) => by simp
                                           intro Hinv _
                                           apply ev.po.nonIncreasing m x Hinv
      }
    }

instance [Preorder v] [Machine CTX M] : LawfulStrongProfunctor (AnticipatedEvent v M) where
  -- XXX : at some point the laws should be demonstrated

instance [Preorder v] [WellFoundedLT v] [Machine CTX M] : Profunctor (ConvergentEvent v M) where
  dimap {α β} {γ δ} (f : β → α) (g : γ → δ) (ev : ConvergentEvent v M α γ) : ConvergentEvent v M β δ :=
    let event := Profunctor.dimap f g ev.to_Event
    {
      guard := fun m x => ev.guard m (f x)
      action := fun m x => event.action m x
      po := {
        safety := fun m x => by simp [Profunctor.dimap]
                                intros Hinv Hgrd
                                let ev' := ConvergentEvent_from_CoConvergentEvent (ContravariantFunctor.contramap f (CoConvergentEvent_from_ConvergentEvent ev))
                                let ev'' := g <$> ev'
                                have Hsafe := ev''.po.safety m x Hinv
                                revert Hsafe ev' ev'' ; simp
                                intro Hsafe
                                exact Hsafe Hgrd

        variant := ev.po.variant

        nonIncreasing := fun m x => by simp
                                       intros Hinv Hgrd
                                       let ev' := ConvergentEvent_from_CoConvergentEvent (ContravariantFunctor.contramap f (CoConvergentEvent_from_ConvergentEvent ev))
                                       let ev'' := g <$> ev'
                                       have Hni := ev''.po.nonIncreasing m x Hinv
                                       revert Hni ev' ev'' ; simp [Functor.map, ContravariantFunctor.contramap]
                                       intro Hni
                                       apply Hni ; exact Hgrd

        convergence := fun m x => by simp
                                     intros Hinv Hgrd
                                     let ev' := ConvergentEvent_from_CoConvergentEvent (ContravariantFunctor.contramap f (CoConvergentEvent_from_ConvergentEvent ev))
                                     let ev'' := g <$> ev'
                                     have Hni := ev''.po.convergence m x Hinv
                                     revert Hni ev' ev'' ; simp [Functor.map, ContravariantFunctor.contramap]
                                     intro Hni
                                     apply Hni ; exact Hgrd
      }
    }

instance [Preorder v] [WellFoundedLT v] [Machine CTX M] : LawfulProfunctor (ConvergentEvent v M) where
  dimap_id := rfl
  dimap_comp _ _ _ _ := rfl

instance [Preorder v] [WellFoundedLT v] [Machine CTX M] : StrongProfunctor (ConvergentEvent v M) where
  first' {α β γ} (ev : ConvergentEvent v M α β): ConvergentEvent v M (α × γ) (β × γ) :=
    let event := StrongProfunctor.first' ev.to_Event
    {
      guard := fun m (x, y) => ev.guard m x ∧ event.guard m (x, y)
      action := event.action
      po := {
        safety := fun m x => by simp
                                intros Hinv _
                                apply ev.po.safety ; assumption

        variant := ev.po.variant

        nonIncreasing := fun m (x,y) => by simp
                                           intro Hinv _
                                           apply ev.po.nonIncreasing m x Hinv
        convergence := fun m (x,y) => by simp
                                         intro Hinv _
                                         apply ev.po.convergence m x Hinv

      }
    }

instance [Preorder v] [WellFoundedLT v] [Machine CTX M] : LawfulStrongProfunctor (ConvergentEvent v M) where
  -- XXX : at some point the laws should be demonstrated

/-

There are no Category or Arrow instances
 - for example, Category.id  has no nonIncreasing argument
   ==> or use a default zero ?
 - Category.comp is maybe possible (but non-trivial combination of variants)

==> probably needs more specific type classes to fix the precise constraints

-/
