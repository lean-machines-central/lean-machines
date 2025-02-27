
import LeanMachines.Event.Prelude
import LeanMachines.Event.Basic
import LeanMachines.Algebra.Contravariant
import LeanMachines.Algebra.Profunctor
import LeanMachines.Algebra.Arrow

/-!
# Ordinary Deterministic events

This module defines the user-level API for constructing
and manipulating **ordinary deterministic** events.

In LeanMachines, an event is said **ordinary** if it
is not demonstrated anticipated or convergent
(cf. `Event.Convergent` module).

-/

/- Typeclass representing the proof  obligation of safety for Events -/
class SafeEvent [Machine CTX M] {α β} (ev : Event M α β) (kind : EventKind) where
  safety (m : M) (x : α):
    Machine.invariant m
    → (grd : ev.guard m x)
    → Machine.invariant (ev.action m x grd).snd





/-- The specification of a deterministic, ordinary event for machine `M`
with input type `α` and output type `β`. .

-/
structure OrdinaryEvent (M) [Machine CTX M] (α β : Type) where
  /-- The guard property of the event, in machine state `m` with input `x`. -/
  guard (m : M) (x : α) : Prop := True
  /-- The (deterministic) action of the event, with
      previous machine state `m` and input `x`, building a pair
      `(y, m')` with `y` an output value and `m'` the next machine state.
      The `grd` parameter is an evidence that the guard is true
      for the specified state and input.
       -/
  action (m : M) (x : α) (grd : guard m x) : β × M

  /-- The safety proof obligation. -/
  safety (m : M) (x : α) :
    Machine.invariant m
    → (grd : guard m x)
    → Machine.invariant (action m x grd).2




/-
  Smart constructor for OrdinaryEvents using the typeclass SafeEvent to get the PO

  It allows to get an element of the structure on which algebraic properties are shown in the
  module Event.Algebra.Ordinary from an event and an instanciation of the typeclass specifying the
  proof obligation
-/
def mkOrdinaryEvent [Machine CTX M] (ev : Event M α β) [instSafe: SafeEvent ev (EventKind.TransDet (Convergence.Ordinary))] : OrdinaryEvent M α β := {
  guard := ev.guard
  action := ev.action
  safety := instSafe.safety
}

@[simp]
def Event.toOrdinaryEvent [Machine CTX M]
  (ev : Event M α β)
  (Hsafe : (m : M) → (x : α) →  Machine.invariant m
                           → (grd : ev.guard m x)
                           → Machine.invariant (ev.action m x grd).snd) : OrdinaryEvent M α β :=
  { guard := ev.guard
    action := ev.action
    safety := Hsafe
  }
@[simp]
def OrdinaryEvent.toEvent [Machine CTX M] (ev : OrdinaryEvent M α β) : Event M α β :=
  {
    guard := ev.guard
    action := ev.action
    kind := EventKind.TransDet (Convergence.Ordinary)
  }


theorem OrdinaryEvent.ext [Machine CTX M] (ev₁ : OrdinaryEvent M α β) (ev₂ : OrdinaryEvent M α β):
  ev₁.toEvent = ev₂.toEvent
  → ev₁ = ev₂ :=
by
  cases ev₁ ; cases ev₂ ; simp



instance [Machine CTX M] (ev : OrdinaryEvent M α β):  SafeEvent ev.toEvent (EventKind.TransDet (Convergence.Ordinary)) where
  safety := ev.safety




def skipEvent (M) [Machine CTX M] (α) : OrdinaryEvent M α α :=
  ((skip_Event M α).toOrdinaryEvent
                                 (by intros ; simp [skip_Event] ; assumption))

/-!

## Initialization events (deterministic)

Initialization events, of the deterministic kind,
are ordinary deterministic events with the *default* state as a pre-state.

They are represented by a typeclass with the property that if an InitEvent instanciates it,
the conversion to Event instanciates the SafeEvent typeclass.
 -/

class SafeInitEvent [Machine CTX M] {α β} (ev : InitEvent M α β) where
  safety (x : α):
    (grd : ev.guard x)
    → Machine.invariant (ev.init x grd).snd


instance [DecidableEq M][Machine CTX M] [Inhabited M] (ev : InitEvent M α β ) [instSafeInit : SafeInitEvent ev] :
 SafeEvent ev.toEvent (EventKind.InitDet) where
  safety m x hinv grd :=
    by simp[grd,instSafeInit.safety]



instance [Machine CTX M ]: SafeEvent (skip_Event (M) α) (EventKind.TransDet (Convergence.Ordinary))where
  safety :=
    by
      simp[Machine.invariant]
