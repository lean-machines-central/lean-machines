
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
(i.e. an instance of the `Preorder` typeclass).
Note that we add an _EventRoot parameter so that variants are
attached to events and not machines.
 -/
class Variant (v) [Preorder v] [instM : Machine CTX M] (ev : _EventRoot M α) where
  variant : M → v

/-!
### Anticipated events
-/

class AnticipatedEventPO (v) [Preorder v] [instM : Machine CTX M] (ev : Event M α β) (kind : EventKind)
  extends Variant v (instM := instM) ev.to_EventRoot, SafeEventPO ev kind where
  nonIncreasing (m : M) (x : α):
    Machine.invariant m
    → (grd : ev.guard m x)
    → let (_, m') := ev.action m x grd
      variant m' ≤ variant m

/-- The specification of an anticipated event.
-/
structure AnticipatedEvent (v) [Preorder v] (M) [instM : Machine CTX M]
    (α β : Type) extends OrdinaryEvent M α β where
  variant : M → v
  nonIncreasing (m : M) (x : α):
    Machine.invariant m
    → (grd : guard m x)
    → let (_, m') := action m x grd
      variant m' ≤ variant m

theorem AnticipatedEvent.ext [Preorder v] {CTX} {M} [Machine CTX M] {α β} (ev₁ ev₂: AnticipatedEvent v M α β):
  ev₁.toOrdinaryEvent = ev₂.toOrdinaryEvent
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
def mkAnticipatedEvent (v) [Preorder v] [Machine CTX M] (ev : Event M α β)
  [instAnticipated : AnticipatedEventPO v ev (EventKind.TransDet (Convergence.Anticipated))] : AnticipatedEvent v M α β :=
  {
    action := ev.action
    guard := ev.guard
    safety := instAnticipated.safety
    nonIncreasing := instAnticipated.nonIncreasing
  }

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
    safety := ev.safety
    variant := variant
    nonIncreasing := Hnincr
  }

/-- The main constructor for ordinary events. -/
def newAnticipatedEvent [Preorder v] [Machine CTX M] (ev : AnticipatedEvent v M α β) := ev

structure AnticipatedEvent' (v) [Preorder v] (M) [instM : Machine CTX M]
    (α : Type) extends OrdinaryEvent' M α where
  variant : M → v
  nonIncreasing (m : M) (x : α):
    Machine.invariant m
    → (grd : guard m x)
    → let m' := action m x grd
      variant m' ≤ variant m

instance [Preorder v] [Machine CTX M]: Coe (AnticipatedEvent' v M α) (AnticipatedEvent v M α Unit) where
  coe ev := { guard := ev.guard
              action m x grd := ((), ev.action m x grd)
              safety := ev.safety
              variant := ev.variant
              nonIncreasing := ev.nonIncreasing
            }

def newAnticipatedEvent' [Preorder v] [Machine CTX M] (ev : AnticipatedEvent' v M α)
  : AnticipatedEvent v M α Unit :=
  newAnticipatedEvent ev

structure AnticipatedEvent'' (v) [Preorder v] (M) [instM : Machine CTX M]
    extends OrdinaryEvent'' M where
  variant : M → v
  nonIncreasing (m : M):
    Machine.invariant m
    → (grd : guard m)
    → let m' := action m grd
      variant m' ≤ variant m

instance [Preorder v] [Machine CTX M]: Coe (AnticipatedEvent'' v M) (AnticipatedEvent v M Unit Unit) where
  coe ev := {
    guard m _ := ev.guard m
    action m _ grd :=  ((), ev.action m grd)
    safety m _ grd := ev.safety m grd
    variant := ev.variant
    nonIncreasing m _ grd := ev.nonIncreasing m grd
  }

def newAnticipatedEvent'' [Preorder v] [Machine CTX M] (ev : AnticipatedEvent'' v M)
  : AnticipatedEvent v M Unit Unit :=
  newAnticipatedEvent ev


/-!
### Convergent events
-/

/-- The proof obligations for convergent events. -/
class ConvergentEventPO (v) [Preorder v] [WellFoundedLT v] [instM : Machine CTX M]
  (ev : Event M α β)
  extends Variant v (instM := instM) ev.to_EventRoot, SafeEventPO ev (EventKind.TransDet (Convergence.Convergent)) where
  convergence (m : M) (x : α):
    Machine.invariant m
    → (grd : ev.guard m x)
    → let (_, m') := ev.action m x grd
      variant m' < variant m

instance [Preorder v] [WellFoundedLT v] [instM : Machine CTX M] (ev : Event M α β) [ConvergentEventPO v ev]
  : AnticipatedEventPO (instM := instM) v ev (EventKind.TransDet (Convergence.Convergent)) where
    nonIncreasing := fun m x hinv hgrd => le_of_lt (ConvergentEventPO.convergence m x hinv hgrd)

/-- The specification of a convergent event. -/
structure ConvergentEvent (v) [Preorder v] [WellFoundedLT v] (M) [instM : Machine CTX M]
    (α β : Type) extends OrdinaryEvent M α β where
    variant : M → v
    convergence (m : M) (x : α):
    Machine.invariant m
    → (grd : guard m x)
    → let (_, m') := action m x grd
      variant m' < variant m

/-- Reconstruction of a convergent event from the required proof obligations. -/
def mkConvergentEvent (v) [Preorder v] [WellFoundedLT v] (M) [instM : Machine CTX M] (α β) (ev : Event M α β) [instConv : ConvergentEventPO v ev]
  : ConvergentEvent v M α β :=
  {
    action := ev.action
    safety := instConv.safety
    variant := instConv.variant
    convergence := instConv.convergence
  }


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
  safety := ev.safety
  variant := variant
  convergence := Hconv
 }


@[simp]
private def ConvergentEvent_fromAnticipated {v} [Preorder v] [WellFoundedLT v] {M} [Machine CTX M] (ev : AnticipatedEvent v M α β)
    (hconv : (m : M) → (x : α)
    → Machine.invariant m
    → (grd : ev.guard m x)
    → let m' := (ev.action m x grd).2
      ev.variant m' < ev.variant m) : ConvergentEvent v M α β :=
  {
    guard := ev.guard
    action := ev.action
    safety := ev.safety
    variant := ev.variant
    convergence := hconv
  }

theorem ConvergentEvent.ext [Preorder v] [WellFoundedLT v] {CTX} {M} [Machine CTX M] {α β} (ev₁ ev₂: ConvergentEvent v M α β):
  ev₁.toOrdinaryEvent = ev₂.toOrdinaryEvent
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

/-- The main constructor for convergent events. -/
def newConvergentEvent [Preorder v] [WellFoundedLT v] [Machine CTX M]
  (ev : ConvergentEvent v M α β) := ev

structure ConvergentEvent' (v) [Preorder v] [WellFoundedLT v] (M) [instM : Machine CTX M]
    (α : Type) extends OrdinaryEvent' M α where
  variant : M → v
  convergence (m : M) (x : α):
    Machine.invariant m
    → (grd : guard m x)
    → let m' := action m x grd
      variant m' < variant m

instance [Preorder v] [WellFoundedLT v] [Machine CTX M]:
    Coe (ConvergentEvent' v M α) (ConvergentEvent v M α Unit) where
  coe ev := { guard := ev.guard
              action m x grd := ((), ev.action m x grd)
              safety := ev.safety
              variant := ev.variant
              convergence := ev.convergence
            }

def newConvergentEvent' [Preorder v] [WellFoundedLT v] [Machine CTX M]
  (ev : ConvergentEvent' v M α) : ConvergentEvent v M α Unit := newConvergentEvent ev

structure ConvergentEvent'' (v) [Preorder v] [WellFoundedLT v] (M) [instM : Machine CTX M]
    extends OrdinaryEvent'' M where
  variant : M → v
  convergence (m : M):
    Machine.invariant m
    → (grd : guard m)
    → let m' := action m grd
      variant m' < variant m

instance [Preorder v] [WellFoundedLT v] [Machine CTX M]:
    Coe (ConvergentEvent'' v M) (ConvergentEvent v M Unit Unit) where
  coe ev := { guard m _ := ev.guard m
              action m _ grd := ((), ev.action m grd)
              safety m _ grd := ev.safety m grd
              variant m := ev.variant m
              convergence m _ := ev.convergence m
            }

def newConvergentEvent'' [Preorder v] [WellFoundedLT v] [Machine CTX M]
  (ev : ConvergentEvent'' v M) : ConvergentEvent v M Unit Unit := newConvergentEvent ev
