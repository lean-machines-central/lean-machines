
import LeanMachines.Event.Prelude
import LeanMachines.Event.Basic
import LeanMachines.Algebra.Contravariant
import LeanMachines.Algebra.Profunctor
import LeanMachines.Algebra.Arrow
import LeanMachines.Event.Algebra.Basic

/-!
# Ordinary Deterministic events

This module defines the user-level API for constructing
and manipulating **ordinary deterministic** events.

In LeanMachines, an event is said **ordinary** if it
is not demonstrated anticipated or convergent
(cf. `Event.Convergent` module).

-/

/- Typeclass representing the proof  obligation of safety for Events -/
class SafeEventPO [Machine CTX M] {α β} (ev : Event M α β) (kind : EventKind) where
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

@[simp]
def OrdinaryEvent.toEvent [Machine CTX M] (ev : OrdinaryEvent M α β) : Event M α β :=
  { guard := ev.guard, action := ev.action }

instance [Machine CTX M]: Coe (OrdinaryEvent M α β) (Event M α β) where
  coe ev := ev.toEvent


/-
  This instance is parameterized by the spec structure : if we defined an event with a structure
  but later need to use the fact that it instanciates the typeclass, we can use it to get
  an instance of SafeEventPO for our structure
-/
instance instSafeEventPO_OrdinaryEvent [Machine CTX M]
  (ev : OrdinaryEvent M α β):  SafeEventPO ev.toEvent (EventKind.TransDet (Convergence.Ordinary)) where
  safety := ev.safety

theorem OrdinaryEvent.ext' {CTX} {M} [Machine CTX M] {α β} (ev₁ ev₂: OrdinaryEvent M α β):
  (∀ m x, ev₁.guard m x = ev₂.guard m x
          ∧ ∀ grd₁ grd₂, ev₁.action m x grd₁ = ev₂.action m x grd₂)
  → ev₁ = ev₂ :=
by
  intros H
  have Hax := _Action_ext_ax ev₁.toEvent ev₂
  cases ev₁
  case mk g₁ act₁ =>
    cases ev₂
    case mk g₂ act₂ =>
      simp at*
      constructor
      case left =>
        apply _Guard_ext
        intros m x
        have Hg := (H m x).1
        exact propext Hg
      case right =>
        exact Hax H

theorem OrdinaryEvent.ext {CTX} {M} [Machine CTX M] {α β} (ev₁ ev₂: OrdinaryEvent M α β):
  ev₁.toEvent = ev₂.toEvent
  → ev₁ = ev₂ :=
by
  intro Heq
  cases ev₁
  case mk grd₁ act₁ safe₁ =>
  cases ev₂
  case mk grd₂ act₁ safe₂ =>
    simp
    cases Heq
    · simp

/-- It is possible to reconstruct an OrdinaryEvent from a plain Event
by providing the safety PO explicitly
XXX: is this useful somewhere ?
-/
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


/--
  It is possible to reconstruct an OrdinaryEvent
  from basic Event with associated proof obligations made
  throught the corresponding typeclasses (SafeEvent, etc.)

  It allows to get an element of the structure on which algebraic properties are shown in the
  module Event.Algebra.Ordinary from an event and an instanciation of the typeclass specifying the
  proof obligation
-/
def mkOrdinaryEvent [Machine CTX M] (ev : Event M α β) [instSafe: SafeEventPO ev (EventKind.TransDet (Convergence.Ordinary))] : OrdinaryEvent M α β := {
  guard := ev.guard
  action := ev.action
  safety := instSafe.safety
}


/-- The main constructor for ordinary events. -/
@[simp]
def newEvent [Machine CTX M] (ev : OrdinaryEvent M α β) := ev

/-- Specification of an [OrdinaryEvent] with Unit as output type.
 (this is like a deterministic Event-B event) -/
structure OrdinaryEvent' (M) [Machine CTX M] (α : Type) where
  guard (m : M) (x : α) : Prop := True
  action (m : M) (x : α) (grd : guard m x) : M

  /-- The safety proof obligation. -/
  safety (m : M) (x : α) :
    Machine.invariant m
    → (grd : guard m x)
    → Machine.invariant (action m x grd)

instance Ord' [Machine CTX M]: Coe (OrdinaryEvent' M α) (OrdinaryEvent M α Unit) where
  coe ev := { guard := ev.guard
              action m x grd := ((), ev.action m x grd)
              safety := ev.safety }

/-- The main constructor for ordinary events. -/
@[simp]
def newEvent' [Machine CTX M] (ev : OrdinaryEvent' M α)
  : OrdinaryEvent M α Unit := ev

/-- Specification of an [OrdinaryEvent] with Unit as input an d output types -/
structure OrdinaryEvent'' (M) [Machine CTX M] where
  guard (m : M) : Prop := True
  action (m : M) (grd : guard m) : M

  /-- The safety proof obligation. -/
  safety (m : M) :
    Machine.invariant m
    → (grd : guard m)
    → Machine.invariant (action m grd)

instance Ord'' [Machine CTX M]: Coe (OrdinaryEvent'' M) (OrdinaryEvent M Unit Unit) where
  coe ev := { guard m _ := ev.guard m
              action m _ grd := ((), ev.action m grd)
              safety m _ := by intros Hinv Hgrd
                               simp
                               exact ev.safety m Hinv Hgrd
  }

/-- The main constructor for ordinary events. -/
@[simp]
def newEvent'' [Machine CTX M] (ev : OrdinaryEvent'' M)
  : OrdinaryEvent M Unit Unit := ev

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

/-- Proof obligation: safety for (determinstic) initialization events -/
class SafeInitEventPO [Machine CTX M] {α β} (ev : _InitEvent M α β) where
  safety (x : α):
    (grd : ev.guard x)
    → Machine.invariant (ev.init x grd).snd

/-- The specification of an initialization event. -/
structure InitEvent (M) [Machine CTX M] (α β : Type)
  extends _InitEvent M α β where

  /-- The safety proof obligation. -/
  safety (x : α) :
    (grd : guard x)
    → Machine.invariant (init x grd).2

instance [Machine CTX M]: Coe (InitEvent M α β) (_InitEvent M α β) where
  coe ev := ev.to_InitEvent

/- Parameterized instance, allowing us to get an instance of the SafeInitEventPO typeclass from the InitEvent spec -/
instance safeInitEventPO_InitEvent[Machine CTX M] (ev : InitEvent M α β):  SafeInitEventPO ev.to_InitEvent where
  safety := ev.safety


/-- Reconstruction of an initialization from its instances. -/
def mkInitEvent [Machine CTX M] (ev : InitEvent M α β) [instSafe: SafeInitEventPO ev.to_InitEvent] : InitEvent M α β := {
  guard := ev.guard
  init := ev.init
  safety := instSafe.safety
}

/-- Main constructor for (deterministic) initialization events.
-/
@[simp]
def newInitEvent [Machine CTX M] (ev : InitEvent M α β) : InitEvent M α β := ev


instance instSafeInitEventPO_InitEvent [Machine CTX M]
  (ev : InitEvent M α β):  SafeInitEventPO ev.to_InitEvent where
  safety := ev.safety


/-- Specification of an [InitEvent] with Unit as output type. -/
structure InitEvent' (M) [Machine CTX M] (α : Type) where
  guard (x : α) : Prop := True
  init (x : α) (grd : guard x) : M

  /-- The safety proof obligation. -/
  safety (x : α) :
    (grd : guard x)
    → Machine.invariant (init x grd)

instance Init' [Machine CTX M]: Coe (InitEvent' M α) (InitEvent M α Unit) where
  coe ev := { guard := ev.guard
              init x grd := ((), ev.init x grd)
              safety := ev.safety }

@[simp]
def newInitEvent' [Machine CTX M] (ev : InitEvent' M α) : InitEvent M α Unit := ev

structure InitEvent'' (M) [Machine CTX M] where
  guard : Prop := True
  init (grd : guard) : M

  /-- The safety proof obligation. -/
  safety :
    (grd : guard)
    → Machine.invariant (init grd)

instance Init'' [Machine CTX M]: Coe (InitEvent'' M) (InitEvent M Unit Unit) where
  coe ev := { guard _ := ev.guard
              init x grd := ((), ev.init grd)
              safety := fun x grd => by exact ev.safety grd }

@[simp]
def newInitEvent'' [Machine CTX M] (ev : InitEvent'' M) : InitEvent M Unit Unit := ev

/-!
## Skip event
-/
instance instSkip [Machine CTX M ]: SafeEventPO (skip_Event (M) α) (EventKind.TransDet (Convergence.Ordinary))where
  safety :=
    by
      simp[Machine.invariant]
