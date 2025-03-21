import LeanMachines.Event.Basic
import LeanMachines.NonDet.Basic

/-!
# Ordinary Non-deterministic events

This module defines the user-level API for constructing
and manipulating **ordinary non-deterministic** events.
(cf. `Even/Ordinary` module for the deterministic case).

There are importance differences with deterministic events:

- the functional action of deterministic events is replaced by a
relational notion of effect

- a feasibility proof obligation is added to the safety requirement

-/

/-!
## Transitional events
-/

/-- The typeclass representation of proof obligations for ordinary
non-deterministic events. -/
class SafeNDEventPO [Machine CTX M] (ev : NDEvent M α β) (kind : EventKind) where
  /-- The safety requirement of non-deterministic events. -/
  safety (m : M) (x : α):
    Machine.invariant m
    → (grd : ev.guard m x)
    → ∀ y, ∀ m', ev.effect m x grd (y, m')
                 → Machine.invariant m'

  /-- The feasibility requirement. -/
  feasibility (m : M) (x : α):
    Machine.invariant m
    → (grd : ev.guard m x)
    → ∃ y, ∃ m', ev.effect m x grd (y, m')

/-- The specification of non-deterministic events without convergence properties.
It is an event for machine type `M` with input type `α` and output type `β` -/
structure OrdinaryNDEvent (M) [Machine CTX M] (α) (β) extends NDEvent M α β where
  /-- The safety requirement of non-deterministic events. -/
  safety (m : M) (x : α):
    Machine.invariant m
    → (grd : guard m x)
    → ∀ y, ∀ m', effect m x grd (y, m')
                 → Machine.invariant m'

  /-- The feasibility requirement. -/
  feasibility (m : M) (x : α):
    Machine.invariant m
    → (grd : guard m x)
    → ∃ y, ∃ m', effect m x grd (y, m')

instance [Machine CTX M]: Coe (OrdinaryNDEvent M α β) (NDEvent M α β) where
  coe ev := ev.toNDEvent

instance [Machine CTX M] (ev : OrdinaryNDEvent M α β):  SafeNDEventPO ev.toNDEvent (EventKind.TransNonDet (Convergence.Ordinary)) where
  safety := ev.safety
  feasibility := ev.feasibility

theorem OrdinaryNDEvent.ext [Machine CTX M] (ev₁ : OrdinaryNDEvent M α β) (ev₂ : OrdinaryNDEvent M α β):
  ev₁.toNDEvent = ev₂.toNDEvent
  → ev₁ = ev₂ :=
by
  cases ev₁ ; cases ev₂ ; simp

@[simp]
def OrdinaryEvent.toOrdinaryNDEvent [Machine CTX M] (ev : OrdinaryEvent M α β) : OrdinaryNDEvent M α β :=
  let event : NDEvent M α β := ev.toEvent
{
  guard := event.guard
  effect := event.effect
  safety := fun m x => by
    simp [event]
    intros Hinv Hgrd y m' Heff
    have Hsafe := ev.safety m x Hinv Hgrd
    simp [←Heff] at Hsafe
    assumption

  feasibility := fun m x => by simp [event]

}

/--
  It is possible to reconstruct an OrdinaryNDEvent
  from basic NDEvent with associated proof obligations made
  throught the corresponding typeclasses (SafeEvent, etc.)
-/
def mkOrdinaryNDEvent [Machine CTX M] (ev : NDEvent M α β) [instSafe: SafeNDEventPO ev (EventKind.TransNonDet (Convergence.Ordinary))] : OrdinaryNDEvent M α β := {
  guard := ev.guard
  effect := ev.effect
  safety := instSafe.safety
  feasibility := instSafe.feasibility
}

/-- The main constructor for non-deterministic ordinary events. -/
@[simp]
def newNDEvent {M} [Machine CTX M] (ev : OrdinaryNDEvent M α β) : OrdinaryNDEvent M α β := ev

/-- Specification of an [OrdinaryNDEvent] with Unit as output type.
 (this is like a deterministic Event-B event) -/
structure OrdinaryNDEvent' (M) [Machine CTX M] (α) where
  guard (m : M) (x : α) : Prop := True
  effect (m : M) (x : α) (grd : guard m x) (m' : M) : Prop
  /-- The safety requirement of non-deterministic events. -/
  safety (m : M) (x : α):
    Machine.invariant m
    → (grd : guard m x)
    → ∀ m', effect m x grd m'
            → Machine.invariant m'

  /-- The feasibility requirement. -/
  feasibility (m : M) (x : α):
    Machine.invariant m
    → (grd : guard m x)
    → ∃ m', effect m x grd m'

instance [Machine CTX M]: Coe (OrdinaryNDEvent' M α) (OrdinaryNDEvent M α Unit) where
  coe ev := { guard := ev.guard
              effect := fun m x grd ((), m') => ev.effect m x grd m'
              safety := fun m x Hinv Hgrd () => ev.safety m x Hinv Hgrd
              feasibility := fun m x Hinv Hgrd => by simp
                                                     exact ev.feasibility m x Hinv Hgrd  }

/-- The main constructor for non-deterministic ordinary events with Unit output type. -/
@[simp]
def newNDEvent' {M} [Machine CTX M] (ev : OrdinaryNDEvent' M α) : OrdinaryNDEvent M α Unit := ev

/-- Specification of an [OrdinaryNDEvent] with Unit as input and output types.
 (this is like a deterministic Event-B event) -/
structure OrdinaryNDEvent'' (M) [Machine CTX M] where
  guard (m : M) : Prop := True
  effect (m : M) (grd : guard m) (m' : M) : Prop
  /-- The safety requirement of non-deterministic events. -/
  safety (m : M):
    Machine.invariant m
    → (grd : guard m)
    → ∀ m', effect m grd m'
            → Machine.invariant m'

  /-- The feasibility requirement. -/
  feasibility (m : M):
    Machine.invariant m
    → (grd : guard m)
    → ∃ m', effect m grd m'

instance [Machine CTX M]: Coe (OrdinaryNDEvent'' M) (OrdinaryNDEvent M Unit Unit) where
  coe ev := { guard := fun m () => ev.guard m
              effect := fun m () grd ((), m') => ev.effect m grd m'
              safety := fun m () Hinv Hgrd () => ev.safety m Hinv Hgrd
              feasibility := fun m () Hinv Hgrd => by simp ; exact ev.feasibility m Hinv Hgrd}

/-- The main constructor for non-deterministic ordinary events with Unit output type. -/
@[simp]
def newNDEvent'' {M} [Machine CTX M] (ev : OrdinaryNDEvent'' M) : OrdinaryNDEvent M Unit Unit := ev


/-!
## Initialiazation events
-/

/-- The internal representation of proof obligations for initialization events. -/
structure _InitNDEventPO [Machine CTX M] (ev : _InitNDEvent M α β) (kind : EventKind) where
  safety (x : α):
    (grd : ev.guard x)
    → ∀ y, ∀ m', ev.init x grd (y, m')
                 → Machine.invariant m'

  feasibility (x : α):
    (grd : ev.guard x)
    → ∃ y, ∃ m', ev.init x grd (y, m')

/-- Type type of non-deterministic initialization events.
It is an event for machine type `M` with input type `α` and output type `β` -/
structure InitNDEvent (M) [Machine CTX M] (α) (β) extends _InitNDEvent M α β where
  po : _InitNDEventPO to_InitNDEvent  EventKind.InitNonDet

/-- The specification of a non-deterministic intialization event for machine `M`
with input type `α` and output type `β`.
The effect of the event is called an `init`.
-/
structure InitNDEventSpec (M) [Machine CTX M] (α) (β) where
  /-- The guard property of the event, an initialization with input `x`. -/
  guard (x : α) : Prop := True
  /-- The (non-deterministic) effect of the event, with
      previous machine state `m` and input `x`, with relation to  pair
      `(y, m')` with `y` an output value and `m'` the next machine state. -/
  init (x : α) (grd : guard x) (_ : β × M) : Prop
  /-- The safety proof obligation. -/
  safety (x : α):
    (grd : guard x)
    → ∀ y, ∀ m, init x grd (y, m)
                → Machine.invariant m
  /-- The feasibility proof obligation. -/
  feasibility (x : α):
    (grd : guard x)
    → ∃ y, ∃ m, init x grd (y, m)

@[simp]
def InitNDEventSpec.to_InitNDEvent [Machine CTX M]
  (ev : InitNDEventSpec M α β) : _InitNDEvent M α β :=
  {
    guard := ev.guard
    init := ev.init
  }

/-- Construction of a on-deterministic initialization event from a
`InitNDEventSpec` specification. -/
@[simp]
def newInitNDEvent {M} [Machine CTX M] (ev : InitNDEventSpec M α β) : InitNDEvent M α β :=
  {
    to_InitNDEvent := ev.to_InitNDEvent
    po := {
      safety := fun x => by simp ; intros ; apply ev.safety x <;> assumption
      feasibility := fun x => by
        intros Hgrd
        exact ev.feasibility x Hgrd
    }
  }

/-- Variant of `InitNDEventSpec` with implicit `Unit` output type -/
structure InitNDEventSpec' (M) [Machine CTX M] (α) where
  guard (x : α) : Prop := True
  init (x : α) (grd : guard x) (m : M) : Prop

  safety (x : α):
    (grd : guard x)
    → ∀ m, init x grd m
           → Machine.invariant m

  feasibility (x : α):
    (grd : guard x)
    → ∃ m, init x grd m

@[simp]
def InitNDEventSpec'.toInitNDEventSpec [Machine CTX M] (ev : InitNDEventSpec' M α) : InitNDEventSpec M α Unit :=
  {
    guard := ev.guard
    init := fun x grd ((), m) => ev.init x grd m
    safety := fun x => by
      simp
      intros Hgrd m Hini
      apply ev.safety x Hgrd ; assumption
    feasibility := fun x => by
      simp
      intros Hgrd
      apply ev.feasibility x Hgrd
  }

/-- Variant of `newInitNDEvent` with implicit `Unit` output type -/
@[simp]
def newInitNDEvent' [Machine CTX M] (ev : InitNDEventSpec' M α) : InitNDEvent M α Unit :=
  newInitNDEvent ev.toInitNDEventSpec


/-- Variant of `InitNDEventSpec` with implicit `Unit` input and output types -/
structure InitNDEventSpec'' (M) [Machine CTX M] where
  guard : Prop := True
  init (grd : guard) (m : M) : Prop

  safety:
    (grd : guard)
    → ∀ m, init grd m
           → Machine.invariant m

  feasibility:
    (grd : guard)
    → ∃ m, init grd m

@[simp]
def InitNDEventSpec''.toInitNDEventSpec [Machine CTX M] (ev : InitNDEventSpec'' M) : InitNDEventSpec M Unit Unit :=
  {
    guard := fun () => ev.guard
    init := fun () grd ((), m) => ev.init grd m
    safety := fun x => by
      simp
      intros Hgrd m Hini
      apply ev.safety Hgrd ; assumption
    feasibility := fun x => by
      simp
      intros Hgrd
      apply ev.feasibility Hgrd
  }

/-- Variant of `newInitNDEvent` with implicit `Unit` input and output types -/
@[simp]
def newInitNDEvent'' [Machine CTX M] (ev : InitNDEventSpec'' M) : InitNDEvent M Unit Unit :=
  newInitNDEvent ev.toInitNDEventSpec
