
import Mathlib.Algebra.Algebra.Basic

import LeanMachines.Event.Prelude
import LeanMachines.Event.Basic
import LeanMachines.Event.Ordinary

/-!

# Non-deterministic events (internal representation)

This module contains the basic (internal) definitions for
non-deterministic events.

-/

/-- The internal representation of all *non-deterministic* transitional events
with: `M` the machine type,
`α` the input type, and `β` the output type of the event
This extends `_EventRoot` with a notion of (non-deterministic/relational) effect.
.-/
@[ext]
structure _NDEvent (M) [Machine CTX M] (α β : Type) where
  guard (m : M) (x : α) : Prop := True
  effect (m : M) (x : α) (grd : guard m x) (eff : β × M): Prop

@[simp]
def prop_NDEvent (M) [Machine CTX M] (p : α → β → Prop) : _NDEvent M α β :=
  { guard _ _ := True
    effect m x _ := fun (y, m') => (m' = m) ∧ p x y }

@[simp]
def _Event.to_NDEvent [Machine CTX M] (ev : _Event M α β) : _NDEvent M α β :=
{
  guard := ev.guard
  effect := fun m x grd (x'', m'') => let (x', m') := ev.action m x grd
                                  m'' = m' ∧ x'' = x'
}

/- XXX : does this axiom breaks something ?
         (I don't think it's provable because of HEq) -/
axiom _Effect_ext_ax {CTX} {M} [Machine CTX M] {α β} (ev₁ ev₂: _NDEvent M α β):
   (∀ m x, ev₁.guard m x = ev₂.guard m x
          ∧ ∀ y m' grd₁ grd₂,
             ev₁.effect m x grd₁ (y, m') ↔ ev₂.effect m x grd₂ (y, m'))
   → HEq ev₁.effect ev₂.effect

theorem _NDEvent.ext' {CTX} {M} [Machine CTX M] {α β} (ev₁ ev₂: _NDEvent M α β):
  (∀ m x, ev₁.guard m x = ev₂.guard m x
          ∧ ∀ y m' grd₁ grd₂, ev₁.effect m x grd₁ (y, m') ↔ ev₂.effect m x grd₂ (y, m'))
  → ev₁ = ev₂ :=
by
  intros H
  have Hax := _Effect_ext_ax ev₁ ev₂
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

/-- The internal representation of *non-deterministic* initialization events
with: `M` the machine type,
`α` the input type, and `β` the output type of the event
.-/
structure _InitNDEvent (M) [Machine CTX M] (α) (β : Type) where
  guard: α → Prop
  init (x : α) (grd : guard x) (eff: β × M) : Prop

@[simp]
def _InitEvent.to_InitNDEvent [Machine CTX M] (ev : _InitEvent M α β) : _InitNDEvent M α β :=
{
  guard := ev.guard
  init := fun x grd (x'', m'') => let (x', m') := ev.init x grd
                                  m'' = m' ∧ x'' = x'
}

@[simp]
def _InitNDEvent.to_NDEvent [Machine CTX M] (ev : _InitNDEvent M α β) : _NDEvent M α β :=
{
  guard := fun m x => m = default ∧ ev.guard x
  effect := fun _ x grd (y, m') => ev.init x grd.2 (y, m')
}

@[simp]
def skip_NDEvent [Machine CTX M] : _NDEvent M α β :=
  {
    effect := fun m _ _ (_, m') => m' = m
  }
