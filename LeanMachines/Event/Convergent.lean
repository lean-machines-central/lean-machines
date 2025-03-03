
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


class Variant (v) [Preorder v] [instM : Machine CTX M] (ev : Event M α β) where
  variant : M → v

/-!
### Anticipated events
-/


class AnticipatedEvent (v) [Preorder v] [instM : Machine CTX M] (ev : Event M α β) (kind : EventKind)
  extends Variant v (instM := instM) ev, SafeEvent ev kind where
  nonIncreasing (m : M) (x : α):
    Machine.invariant m
    → (grd : ev.guard m x)
    → let (_, m') := ev.action m x grd
      variant m' ≤ variant m

/-- The "downgrading" of an anticipated event to an ordinary one is automatic because we extend the structure ! -/

structure _AnticipatedEvent (v) [Preorder v] (M) [instM : Machine CTX M]
    (α β : Type) extends OrdinaryEvent M α β where
  variant : M → v
  nonIncreasing (m : M) (x : α):
    Machine.invariant m
    → (grd : guard m x)
    → let (_, m') := action m x grd
      variant m' ≤ variant m


def mkAnticipatedEvent (v) [Preorder v] [Machine CTX M] (ev : Event M α β)
  [instAnticipated : AnticipatedEvent v ev (EventKind.TransDet (Convergence.Anticipated))] : _AnticipatedEvent v M α β :=
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
      variant m' ≤ variant m) : _AnticipatedEvent v M α β :=
  {
    guard := ev.guard
    action := ev.action
    safety := ev.safety
    variant := variant
    nonIncreasing := Hnincr
  }





/-!
### Convergent events
-/


-- class ConvergentEvent (v) [Preorder v]  [WellFoundedLT v] [Machine CTX M]
--   (ev : Event M α β )
--   extends AnticipatedEvent v ev (EventKind.TransDet (Convergence.Convergent)) where

--   convergence (m : M) (x : α):
--     Machine.invariant m
--     → (grd : ev.guard m x)
--     → let (_, m') := ev.action m x grd
--       variant m' < variant m

--   nonIncreasing (m : M) (x : α) := fun hinv hgrd => le_of_lt (convergence m x hinv hgrd)

class ConvergentEvent (v) [Preorder v] [WellFoundedLT v] [instM : Machine CTX M]
  (ev : Event M α β)
  extends Variant v (instM := instM) ev, SafeEvent ev (EventKind.TransDet (Convergence.Convergent)) where
  convergence (m : M) (x : α):
    Machine.invariant m
    → (grd : ev.guard m x)
    → let (_, m') := ev.action m x grd
      variant m' < variant m


instance [Preorder v] [WellFoundedLT v] [instM : Machine CTX M] (ev : Event M α β) [ConvergentEvent v ev]
  : AnticipatedEvent (instM := instM) v ev (EventKind.TransDet (Convergence.Convergent)) where
    nonIncreasing := fun m x hinv hgrd => le_of_lt (ConvergentEvent.convergence m x hinv hgrd)



structure _ConvergentEvent (v) [Preorder v] [WellFoundedLT v] (M) [instM : Machine CTX M]
    (α β : Type) extends OrdinaryEvent M α β where
    variant : M → v
    convergence (m : M) (x : α):
    Machine.invariant m
    → (grd : guard m x)
    → let (_, m') := action m x grd
      variant m' < variant m


def mkConvergentEvent (v) [Preorder v] [WellFoundedLT v] (M) [instM : Machine CTX M] (α β) (ev : Event M α β) [instConv : ConvergentEvent v ev]
  : _ConvergentEvent v M α β :=
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
 : _ConvergentEvent v M α β :=
 {
  guard := ev.guard
  action := ev.action
  safety := ev.safety
  variant := variant
  convergence := Hconv
 }




@[simp]
private def ConvergentEvent_fromAnticipated {v} [Preorder v] [WellFoundedLT v] {M} [Machine CTX M] (ev : _AnticipatedEvent v M α β)
    (hconv : (m : M) → (x : α)
    → Machine.invariant m
    → (grd : ev.guard m x)
    → let m' := (ev.action m x grd).2
      ev.variant m' < ev.variant m) : _ConvergentEvent v M α β :=
  {
    guard := ev.guard
    action := ev.action
    safety := ev.safety
    variant := ev.variant
    convergence := hconv
  }
