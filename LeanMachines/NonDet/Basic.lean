
import Mathlib.Algebra.Algebra.Basic

import LeanMachines.Event.Prelude
import LeanMachines.Event.Basic
import LeanMachines.Event.Ordinary

/-!

# Non-deterministic events (internal representation)

This module contains the basic (internal) definitions for
non-deterministic events.

-/

/-- The representation of all *non-deterministic* transitional events
with: `M` the machine type,
`α` the input type, and `β` the output type of the event
This extends `_EventRoot` with a notion of (non-deterministic/relational) effect.
.-/
@[ext]
structure NDEvent (M) [Machine CTX M] (α : Type) (β : Type)
  extends _EventRoot M α where

  /-- The (non-deterministic) effect of the event, with
      previous machine state `m` and input `x`, with relation to  pair
      `(y, m')` with `y` an output value and `m'` the next machine state. -/
  effect (m : M) (x : α) (grd : guard m x) (eff : β × M): Prop


instance [Machine CTX M]: Coe (Event M α β) (NDEvent M α β) where
  coe ev := { guard := ev.guard
              effect := fun m x grd (y, m') =>
                (y, m') = ev.action  m x grd
  }

class _NDEvent (M) [Machine CTX M] (α : Type) (β : Type) where
  guard (m : M) (x : α) : Prop
  effect (m : M) (x : α) (grd : guard m x) (eff : β × M): Prop

instance [Machine CTX M] (ev : NDEvent M α β): _NDEvent M α β where
  guard := ev.guard
  effect := ev.effect

/- XXX : does this axiom breaks something ?
         (I don't think it's provable because of HEq) -/
axiom _Effect_ext_ax {CTX} {M} [Machine CTX M] {α β} (ev₁ ev₂: NDEvent M α β):
   (∀ m x, ev₁.guard m x = ev₂.guard m x
          ∧ ∀ y m' grd₁ grd₂,
             ev₁.effect m x grd₁ (y, m') ↔ ev₂.effect m x grd₂ (y, m'))
   → HEq ev₁.effect ev₂.effect



theorem Event.ext'' {CTX} {M} [Machine CTX M] {α β} (ev₁ ev₂: Event M α β):
  (∀ m x, ev₁.guard m x = ev₂.guard m x
          ∧ ∀ grd₁ grd₂, ev₁.action m x grd₁ = ev₂.action m x grd₂)
  → ev₁ = ev₂ :=
by
  have Hax := _Action_ext_ax ev₁ ev₂
  intros H
  cases ev₁
  case mk evr₁ act₁ =>
  cases ev₂
  case mk evr₂ act₂ =>
  simp [*] at *
  constructor
  case left =>
    apply _EventRoot.ext'
    intros m x
    have Hmx := H m x
    simp [Hmx]
  case right =>
    apply Hax
    apply H

theorem NDEvent.ext' {CTX} {M} [Machine CTX M] {α β} (ev₁ ev₂: NDEvent M α β):
  (∀ m x, ev₁.guard m x = ev₂.guard m x
          ∧ ∀ y m' grd₁ grd₂, ev₁.effect m x grd₁ (y, m') ↔ ev₂.effect m x grd₂ (y, m'))
  → ev₁ = ev₂ :=
by
  have Hax := _Effect_ext_ax ev₁ ev₂
  intros H
  cases ev₁
  case mk evr₁ act₁ =>
  cases ev₂
  case mk evr₂ act₂ =>
  simp [*] at *
  constructor
  case left =>
    apply _EventRoot.ext'
    intros m x
    have Hmx := H m x
    simp [Hmx]
  case right =>
    apply Hax
    apply H

/-- The internal representation of *non-deterministic* initialization events
with: `M` the machine type,
`α` the input type, and `β` the output type of the event
.-/
structure _InitNDEvent (M) [Machine CTX M] (α) (β : Type) where
  guard: α → Prop
  init (x : α) (grd : guard x) (eff: β × M) : Prop

instance [Machine CTX M]: Coe (_InitEvent M α β) (_InitNDEvent M α β) where
  coe ev := { guard := ev.guard
              init := fun x grd (y, m) => (y, m) = ev.init x grd}

/-- Any relation `α → β → Prop` can be lifted to a non-deterministic event.
   (like for function an deterministic events). -/
@[simp]
def prop_NDEvent (M) [Machine CTX M] (p : α → β → Prop) : NDEvent M α β :=
  {
    guard _ _ := True
    effect m x _ := fun (y, m') => (m' = m) ∧ p x y
  }


@[simp]
def skip_NDEvent [Machine CTX M] : NDEvent M α β :=
  {
    guard _ _ := True
    effect := fun m _ _ (_, m') => m' = m
  }
