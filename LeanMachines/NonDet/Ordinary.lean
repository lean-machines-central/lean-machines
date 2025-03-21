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
## Initialization events
-/

/-- Proof obligation: safety for (non-determinstic) initialization events -/
class SafeInitNDEventPO [Machine CTX M] {α β} (ev : _InitNDEvent M α β) where
  safety (x : α):
    (grd : ev.guard x)
    → ∀ y, ∀ m', ev.init x grd (y, m')
                 → Machine.invariant m'

  feasibility (x : α):
    (grd : ev.guard x)
    → ∃ y, ∃ m', ev.init x grd (y, m')

/-- The specification of non-deterministic initialization events.
It is an event for machine type `M` with input type `α` and output type `β` -/
structure InitNDEvent (M) [Machine CTX M] (α) (β) extends _InitNDEvent M α β where
  /-- The safety requirement of non-deterministic events. -/
  safety (x : α):
    (grd : guard x)
    → ∀ y, ∀ m', init x grd (y, m')
                 → Machine.invariant m'

  /-- The feasibility requirement. -/
  feasibility (x : α):
    (grd : guard x)
    → ∃ y, ∃ m', init x grd (y, m')

instance [Machine CTX M]: Coe (InitNDEvent M α β) (_InitNDEvent M α β) where
  coe ev := ev.to_InitNDEvent

instance [Machine CTX M] (ev : InitNDEvent M α β):  SafeInitNDEventPO ev.to_InitNDEvent where
  safety := ev.safety
  feasibility := ev.feasibility

/-- Reconstruction of an initialization from its instances. -/
def mkInitNDEvent [Machine CTX M] (ev : InitNDEvent M α β) [instSafe: SafeInitNDEventPO ev.to_InitNDEvent] : InitNDEvent M α β := {
  guard := ev.guard
  init := ev.init
  safety := instSafe.safety
  feasibility := instSafe.feasibility
}

/-- Main constructor for (deterministic) initialization events.
-/
@[simp]
def newInitNDEvent [Machine CTX M] (ev : InitNDEvent M α β) : InitNDEvent M α β := ev

/-- Specification of an [InitNDEvent] with Unit as output type. -/
structure InitNDEvent' (M) [Machine CTX M] (α) where
  guard: α → Prop
  init (x : α) (grd : guard x) (m': M) : Prop

  /-- The safety requirement of non-deterministic events. -/
  safety (x : α):
    (grd : guard x)
    → ∀ m', init x grd m'
             → Machine.invariant m'

  /-- The feasibility requirement. -/
  feasibility (x : α):
    (grd : guard x)
    → ∃ m', init x grd m'

instance [Machine CTX M]: Coe (InitNDEvent' M α) (InitNDEvent M α Unit) where
  coe ev := { guard := ev.guard
              init := fun x grd (_,m') => ev.init x grd m'
              safety x grd _  := ev.safety x grd
              feasibility := fun x grd => by exists ()
                                             exact ev.feasibility x grd
            }

/-- Variant of `newInitNDEvent` with implicit `Unit` output type -/
@[simp]
def newInitNDEvent' [Machine CTX M] (ev : InitNDEvent' M α) : InitNDEvent M α Unit := ev


/-- Specification of an [InitNDEvent] with Unit as input and output types. -/
structure InitNDEvent'' (M) [Machine CTX M] where
  guard: Prop
  init (grd : guard) (m': M) : Prop

  /-- The safety requirement of non-deterministic events. -/
  safety:
    (grd : guard)
    → ∀ m', init grd m'
            → Machine.invariant m'

  /-- The feasibility requirement. -/
  feasibility:
    (grd : guard)
    → ∃ m', init grd m'

instance [Machine CTX M]: Coe (InitNDEvent'' M) (InitNDEvent M Unit Unit) where
  coe ev := { guard _ := ev.guard
              init _ := fun grd (_,m') => ev.init grd m'
              safety _ grd _  := ev.safety grd
              feasibility := fun x grd => by exists ()
                                             exact ev.feasibility grd
            }
/-- Variant of `newInitNDEvent` with implicit `Unit` input and output types -/
@[simp]
def newInitNDEvent'' [Machine CTX M] (ev : InitNDEvent'' M) : InitNDEvent M Unit Unit := ev
