
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

/-- The internal representation of proof obligations for ordinary
deterministic events. -/
structure _EventPO [Machine CTX M] (ev : _Event M α β) (kind : EventKind) where
  safety (m : M) (x : α):
    Machine.invariant m
    → (grd : ev.guard m x)
    → Machine.invariant (ev.action m x grd).snd

/-- The type of deterministic events without convergence properties.
It is an event for machine type `M` with input type `α` and output type `β` -/
structure OrdinaryEvent (M) [Machine CTX M] (α) (β) extends _Event M α β where
  po : _EventPO to_Event  (EventKind.TransDet Convergence.Ordinary)

theorem OrdinaryEvent.ext [Machine CTX M] (ev₁ : OrdinaryEvent M α β) (ev₂ : OrdinaryEvent M α β):
  ev₁.to_Event = ev₂.to_Event
  → ev₁ = ev₂ := by cases ev₁ ; cases ev₂ ; simp

theorem OrdinaryEvent.ext' {CTX} {M} [Machine CTX M] {α β} (ev₁ ev₂: OrdinaryEvent M α β):
  (∀ m x, ev₁.guard m x = ev₂.guard m x
          ∧ ∀ grd₁ grd₂, ev₁.action m x grd₁ = ev₂.action m x grd₂)
  → ev₁ = ev₂ :=
by
  intros H
  have Hax := _Action_ext_ax ev₁.to_Event ev₂.to_Event
  cases ev₁
  case mk to_event₁ po₁ =>
    cases ev₂
    case mk to_event₂ po₂ =>
    simp at *
    apply _Event.ext'
    intros m x
    have ⟨H'₁, H'₂⟩ := H m x
    constructor
    · exact propext H'₁
    exact H'₂

  -- case mk g₁ act₁ =>
  --   cases ev₂
  --   case mk g₂ act₂ =>
  --     simp at*
  --     -- constructor
  --     -- case left =>
  --     --   apply _Guard_ext
  --     --   intros m x
  --     --   have Hg := (H m x).1
  --     --   exact propext Hg
  --     -- case right =>
  --     --   exact Hax H


/-- The specification of a deterministic, ordinary event for machine `M`
with input type `α` and output type `β`. . -/
structure EventSpec (M) [Machine CTX M] (α) (β) where
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
def _Event.toEventSpec [Machine CTX M]
  (ev : _Event M α β)
  (Hsafe : (m : M) → (x : α) →  Machine.invariant m
                           → (grd : ev.guard m x)
                           → Machine.invariant (ev.action m x grd).snd) : EventSpec M α β :=
  { guard := ev.guard
    action := ev.action
    safety := Hsafe
  }

@[simp]
def EventSpec.to_Event [Machine CTX M] (ev : EventSpec M α β) : _Event M α β :=
  { guard := ev.guard
    action := ev.action
  }

/-- Construction of an ordinary deterministic event from a
`EventSpec` specification. -/
@[simp]
def newEvent {M} [Machine CTX M] (ev : EventSpec M α β) : OrdinaryEvent M α β :=
  { to_Event := ev.to_Event
    po := {
      safety := fun m x => by
        intros Hinv Hgrd
        apply ev.safety <;> assumption
    }
  }

/-- Variant of `EventSpec` with implicit `Unit` output type -/
structure EventSpec' (M) [Machine CTX M] (α) where
  guard (m : M) (x : α) : Prop := True
  action (m : M) (x : α) (grd : guard m x): M
  safety (m : M) (x : α) :
    Machine.invariant m
    → (grd : guard m x)
    → Machine.invariant (action m x grd)

@[simp]
def EventSpec'.toEventSpec [Machine CTX M] (ev : EventSpec' M α) : EventSpec M α Unit :=
  {
    guard := ev.guard
    action := fun m x grd => ((), ev.action m x grd)
    safety := fun m x => by simp ; apply ev.safety
  }

/-- Variant of `newEvent` with implicit `Unit` output type -/
@[simp]
def newEvent' {M} [Machine CTX M] (ev : EventSpec' M α) : OrdinaryEvent M α Unit :=
  newEvent ev.toEventSpec

/-- Variant of `EventSpec` with implicit `Unit` input and output types -/
structure EventSpec'' (M) [Machine CTX M] where
  guard (m : M) : Prop := True
  action (m : M) (grd : guard m): M
  safety (m : M) :
    Machine.invariant m
    → (grd : guard m)
    → Machine.invariant (action m grd)

@[simp]
def EventSpec''.toEventSpec [Machine CTX M] (ev : EventSpec'' M) : EventSpec M Unit Unit :=
  {
    guard := fun m () => ev.guard m
    action := fun m () grd => ((), ev.action m grd)
    safety := fun m () => by simp ; apply ev.safety
  }

/-- Variant of `newEvent` with implicit `Unit` input and output types -/
@[simp]
def newEvent'' {M} [Machine CTX M] (ev : EventSpec'' M) : OrdinaryEvent M Unit Unit :=
  newEvent ev.toEventSpec

def skipEvent (M) [Machine CTX M] (α) : OrdinaryEvent M α α :=
  newEvent ((skip_Event M α).toEventSpec
                                 (by intros ; simp [skip_Event] ; assumption))

/-!

## Initialization events (deterministic)

Initialization events, of the deterministic kind,
are ordinary deterministic events with the *default* state as a pre-state.

 -/

/-- The internal representation of proof obligations for initialization events. -/
structure _InitEventPO [Machine CTX M] (ev : _InitEvent M α β) (kind : EventKind) where
  safety (x : α):
    (grd : ev.guard x)
    → Machine.invariant (ev.init x grd).snd


/-- Type type of deterministic initialization events.
It is an event for machine type `M` with input type `α` and output type `β` -/
structure InitEvent (M) [Machine CTX M] (α) (β) extends _InitEvent M α β where
  po : _InitEventPO to_InitEvent EventKind.InitDet

/-- The specification of a deterministic ordinary event for machine `M`
with input type `α` and output type `β`. . -/
structure InitEventSpec (M) [Machine CTX M] (α) (β) where
  /-- The guard property of the event, an initialization with input `x`. -/
  guard (x : α) : Prop := True
  /-- The (deterministic) action of the event, with input `x`, building a pair
      `(y, m)` with `y` an output value and `m` an initial machine state.-/
  init (x : α) (grd : guard x): β × M
  /-- The safety proof obligation. -/
  safety (x : α) :
    (grd : guard x)
    → Machine.invariant (init x grd).2

@[simp]
def InitEventSpec.to_InitEvent [Machine CTX M] (ev : InitEventSpec M α β) : _InitEvent M α β :=
  {
    guard := ev.guard
    init := ev.init
  }

/-- Construction of a deterministic initialization event from a
`InitEventSpec` specification. -/
@[simp]
def newInitEvent {M} [Machine CTX M] (ev : InitEventSpec M α β) : InitEvent M α β :=
  {
    to_InitEvent := ev.to_InitEvent
    po := {
      safety := fun x => by simp
                            intro Hgrd
                            apply ev.safety x Hgrd

    }
  }

/-- Variant of `InitEventSpec` with implicit `Unit` output type -/
structure InitEventSpec' (M) [Machine CTX M] (α) where
  guard (x : α) : Prop := True
  init (x : α) (grd : guard x): M
  safety (x : α) :
    (grd : guard x)
    → Machine.invariant (init x grd)

@[simp]
def InitEventSpec'.toInitEventSpec [Machine CTX M] (ev : InitEventSpec' M α) : InitEventSpec M α Unit :=
  {
    guard := ev.guard
    init := fun x grd => ((), ev.init x grd)
    safety := fun x => by simp ; apply ev.safety
  }

/-- Variant of `newInitEvent` with implicit `Unit` output type -/
@[simp]
def newInitEvent' {M} [Machine CTX M] (ev : InitEventSpec' M α) : InitEvent M α Unit :=
  newInitEvent ev.toInitEventSpec

/-- Variant of `InitEventSpec` with implicit `Unit` input and output types -/
structure InitEventSpec'' (M) [Machine CTX M] where
  guard : Prop := True
  init (grd : guard) : M
  safety :
    (grd : guard)
    → Machine.invariant (init grd)

@[simp]
def InitEventSpec''.toInitEventSpec [Machine CTX M] (ev : InitEventSpec'' M) : InitEventSpec M Unit Unit :=
  {
    guard := fun () => ev.guard
    init := fun () grd => ((), ev.init grd)
    safety := fun () => by simp ; apply ev.safety
  }

/-- Variant of `newInitEvent` with implicit `Unit` input and output types -/
@[simp]
def newInitEvent'' {M} [Machine CTX M] (ev : InitEventSpec'' M) : InitEvent M Unit Unit :=
  newInitEvent ev.toInitEventSpec
