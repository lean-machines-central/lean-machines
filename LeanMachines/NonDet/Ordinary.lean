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

/-- The internal representation of proof obligations for ordinary
non-deterministic events. -/
structure _NDEventPO [Machine CTX M] (ev : _NDEvent M α β) (kind : EventKind) where
  safety (m : M) (x : α):
    Machine.invariant m
    → (grd : ev.guard m x)
    → ∀ y, ∀ m', ev.effect m x grd (y, m')
                 → Machine.invariant m'

  feasibility (m : M) (x : α):
    Machine.invariant m
    → (grd : ev.guard m x)
    → ∃ y, ∃ m', ev.effect m x grd (y, m')

/-- The type of non-deterministic events without convergence properties.
It is an event for machine type `M` with input type `α` and output type `β` -/
structure OrdinaryNDEvent (M) [Machine CTX M] (α) (β) extends _NDEvent M α β where
  po : _NDEventPO to_NDEvent  (EventKind.TransNonDet Convergence.Ordinary)

theorem OrdinaryNDEvent.ext [Machine CTX M] (ev₁ : OrdinaryNDEvent M α β) (ev₂ : OrdinaryNDEvent M α β):
  ev₁.to_NDEvent = ev₂.to_NDEvent
  → ev₁ = ev₂ :=
by
  cases ev₁ ; cases ev₂ ; simp


@[simp]
def OrdinaryEvent.toOrdinaryNDEvent [Machine CTX M] (ev : OrdinaryEvent M α β) : OrdinaryNDEvent M α β :=
  let event := ev.to_Event.to_NDEvent
{
  guard := event.guard
  effect := event.effect
  po := {
    safety := fun m x => by simp [event]
                            intro Hinv Hgrd
                            apply ev.po.safety m x Hinv Hgrd

    feasibility := fun m x => by simp [event]
  }
}

/-- The specification of a non-deterministic, ordinary event for machine `M`
with input type `α` and output type `β`. . -/
structure NDEventSpec (M) [Machine CTX M] (α) (β) where
  /-- The guard property of the event, in machine state `m` with input `x`. -/
  guard (m : M) (x : α) : Prop := True

  /-- The (non-deterministic) effect of the event, with
      previous machine state `m` and input `x`, with relation to  pair
      `(y, m')` with `y` an output value and `m'` the next machine state.

      **Remark: the guard property is supposed valid any time the effect
      must hold in the POs. However, this is not captured
      at the type level (a type-level guard-dependent variant is currently being
      investigated). -/
  effect (m : M) (x : α) (grd : guard m x) (_ : β × M) : Prop

  /-- The safety proof obligation. -/
  safety (m : M) (x : α):
    Machine.invariant m
    → (grd : guard m x)
    → ∀ y, ∀ m', effect m x grd (y, m')
                 → Machine.invariant m'

  /-- The feasibility proof obligation.
  This PO may be difficult to establish concretely in some models.
  In this case it is still considered an important
  axiom (which means a Lean4 axiom should be used to discharge the PO).
  -/
  feasibility (m : M) (x : α):
    Machine.invariant m
    → (grd : guard m x)
    → ∃ y, ∃ m', effect m x grd (y, m')

@[simp]
def NDEventSpec.to_NDEvent [Machine CTX M] (ev : NDEventSpec M α β) : _NDEvent M α β :=
  { guard := ev.guard
    effect := ev.effect
  }

/-- Construction of an ordinary non-deterministic event from a
`NDEventSpec` specification. -/
@[simp]
def newNDEvent {M} [Machine CTX M] (ev : NDEventSpec M α β) : OrdinaryNDEvent M α β :=
  {
    to_NDEvent := ev.to_NDEvent
    po := { safety := fun m x => by simp
                                    intros Hinv Hgrd
                                    apply ev.safety ; assumption
            feasibility := fun m x => by simp
                                         intros Hinv Hgrd
                                         apply ev.feasibility ; assumption
    }
  }

/-- Variant of `NDEventSpec` with implicit `Unit` output type -/
structure NDEventSpec' (M) [Machine CTX M] (α) where
  guard (m : M) (x : α) : Prop := True
  effect (m : M) (x : α) (grd : guard m x) (m' : M) : Prop

  safety (m : M) (x : α):
    Machine.invariant m
    → (grd : guard m x)
    → ∀ m', effect m x grd m'
            → Machine.invariant m'

  feasibility (m : M) (x : α):
    Machine.invariant m
    → (grd : guard m x)
    → ∃ m', effect m x grd m'

@[simp]
def NDEventSpec'.toNDEventSpec [Machine CTX M] (ev : NDEventSpec' M α) : NDEventSpec M α Unit :=
  { guard := ev.guard
    effect := fun m x grd ((), m') => ev.effect m x grd m'
    safety := fun m x => by simp ; apply ev.safety
    feasibility := fun m x => by simp ; apply ev.feasibility
  }

/-- Variant of `newNDEvent` with implicit `Unit` output type -/
@[simp]
def newNDEvent' {M} [Machine CTX M] (ev : NDEventSpec' M α) : OrdinaryNDEvent M α Unit :=
  newNDEvent ev.toNDEventSpec

/-- Variant of `NDEventSpec` with implicit `Unit` input and output types -/
structure NDEventSpec'' (M) [Machine CTX M] where
  guard (m : M) : Prop := True
  effect (m : M) (grd : guard m) (m' : M) : Prop

  safety (m : M):
    Machine.invariant m
    → (grd : guard m)
    → ∀ m', effect m grd m'
            → Machine.invariant m'

  feasibility (m : M):
    Machine.invariant m
    → (grd : guard m)
    → ∃ m', effect m grd m'

@[simp]
def NDEventSpec''.toNDEventSpec [Machine CTX M] (ev : NDEventSpec'' M) : NDEventSpec M Unit Unit :=
  { guard := fun m _ => ev.guard m
    effect := fun m () grd ((), m') => ev.effect m grd m'
    safety := fun m x => by
      simp
      intros Hinv Hgrd m' Heff
      exact ev.safety m Hinv Hgrd m' Heff
    feasibility := fun m x => by
      simp
      intros Hinv Hgrd
      exact ev.feasibility m Hinv Hgrd
  }

/-- Variant of `newNDEvent` with implicit `Unit` input and output types -/
@[simp]
def newNDEvent'' {M} [Machine CTX M] (ev : NDEventSpec'' M) : OrdinaryNDEvent M Unit Unit :=
  newNDEvent ev.toNDEventSpec

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
