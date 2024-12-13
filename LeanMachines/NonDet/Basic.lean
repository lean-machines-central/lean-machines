
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
  guard := fun m x => m = Machine.reset ∧ ev.guard x
  effect := fun _ x grd (y, m') => ev.init x grd.2 (y, m')
}

@[simp]
def skip_NDEvent [Machine CTX M] : _NDEvent M α β :=
  {
    effect := fun m _ _ (_, m') => m' = m
  }


/-!
# Algebraic properties of non-deterministic events
(experimental, for now undocumented)
-/


-- Remark: The functor instance is existential, not surprising given the relational context
instance [Machine CTX M] : Functor (_NDEvent M γ) where
  map f ev :=
  {
    guard := ev.guard
    effect := fun m x grd (y, m') => ∃ z, ∃ m'', ev.effect m x grd (z, m'')
                                                 ∧ y = f z ∧ m' = m''
  }

instance [Machine CTX M] : LawfulFunctor (_NDEvent M γ) where
  map_const := rfl
  id_map ev := by simp [Functor.map]

  comp_map g h ev := by
    simp [Functor.map]
    funext m x grd (y,m')
    apply propext
    constructor
    · intro Hz
      cases Hz
      case _ z H =>
        simp at H
        simp
        exists (g z)
        constructor
        · exists z
          simp [H]
        simp [H]
    simp
    intros z t Heff Heq₁ Heq₂
    exists t
    simp [Heff, Heq₁, Heq₂]


-- There are two possible, distinct ContravariantFunctor functors
-- for non-deterministic events.

-- The first operates on the output, hence it cannot be use
-- in a profunctor context
instance [Machine CTX M] : ContravariantFunctor (_NDEvent M γ) where
  contramap f ev :=
  {
    guard := ev.guard
    effect := fun m x grd (y, m') => ev.effect m x grd ((f y), m')
  }

instance [Machine CTX M] : LawfullContravariantFunctor (_NDEvent M β) where
  cmap_id _ := rfl
  cmap_comp _ _ := rfl

-- The second operates on the input
abbrev _CoNDEvent (M) [Machine CTX M] (α) (β) := _NDEvent M β α

@[simp]
def CoNDEvent_from_NDEvent [Machine CTX M] (ev : _NDEvent M α β) : _CoNDEvent M β α :=
 ev

@[simp]
def NDEvent_from_CoNDEvent [Machine CTX M] (ev : _CoNDEvent M β α) : _NDEvent M α β :=
 ev


instance [Machine CTX M] : ContravariantFunctor (_CoNDEvent M γ) where
  contramap f ev :=
  {
     guard := fun m x => ev.guard m (f x)
     effect := fun m x grd (y, m')  => ev.effect m (f x) grd (y, m')
  }

instance [Machine CTX M] : LawfullContravariantFunctor (_CoNDEvent M γ) where
  cmap_id _ := rfl
  cmap_comp _ _ := rfl

-- There is a unique possible profunctor instance
instance [Machine CTX M] : Profunctor (_NDEvent M) where
  dimap {α β} {γ δ} (f : β → α) (g : γ → δ) (ev : _NDEvent M α γ) : _NDEvent M β δ :=
  let ev' := NDEvent_from_CoNDEvent (ContravariantFunctor.contramap f (CoNDEvent_from_NDEvent ev))
  g <$> ev'

instance [Machine CTX M] : LawfulProfunctor (_NDEvent M) where
  dimap_id := by simp [Profunctor.dimap, ContravariantFunctor.contramap]
                 exact fun {α β} => rfl
  dimap_comp f f' g g' := by
    simp [Profunctor.dimap, ContravariantFunctor.contramap, Functor.map]
    funext ev
    simp
    funext m x grd (y,m')
    simp
    constructor
    · intro Heff
      cases Heff
      case _ u Heff =>
        exists (g' u)
        simp [Heff]
        exists u
        simp [Heff]
    intro Heff
    cases Heff
    case _ t Heff =>
      simp at Heff
      cases Heff
      case _ Heff Hy =>
        cases Heff
        case _ u Heff =>
          exists u
          simp [Heff, Hy]

instance [Machine CTX M] : StrongProfunctor (_NDEvent M) where
  first' {α β γ} (ev : _NDEvent M α β): _NDEvent M (α × γ) (β × γ) :=
    {
      guard := fun m (x, _) => ev.guard m x
      effect := fun m (x,u) grd ((y, v), m') => v = u ∧ ev.effect m x grd (y, m')
    }

instance [Machine CTX M] : LawfulStrongProfunctor (_NDEvent M) where


instance [Machine CTX M]: Category (_NDEvent M) where
  id := {
    effect := fun m x _ (y, m') => y = x ∧ m' = m
  }

  comp {α β γ} (ev₂ : _NDEvent M β γ) (ev₁ : _NDEvent M α β) : _NDEvent M α γ :=
    { guard := fun m x => ev₁.guard m x
                          ∧ ((grd : ev₁.guard m x)
                             → (∀ y, ∀ m', ev₁.effect m x grd (y, m')
                                → ev₂.guard m' y))
      effect := fun m x grd (z, m'') =>
        ∃ y m',  ev₁.effect m x grd.1 (y, m') ∧
                 ((eff₁ : ev₁.effect m x grd.1 (y, m')) →
                  ev₂.effect m' y (grd.2 grd.1 y m' eff₁) (z, m''))
    }

instance [Machine CTX M]: LawfulCategory (_NDEvent M) where
  id_right ev := by
    apply _NDEvent.ext'
    simp
    intros m x y m' grd₁ grd₂
    constructor
    · simp
    · intros Heff
      exists x
      exists m
      simp [Heff]

  id_left ev := by
    apply _NDEvent.ext'
    simp
    intros m x y m' grd₁ grd₂
    constructor
    · intro ⟨yy,⟨mm',H₁,H₂'⟩⟩
      have H₂ := H₂' H₁
      simp [H₁,H₂]
    · intro Heff₁
      exists y
      exists m'
      simp [Heff₁]

  id_assoc ev₁ ev₂ ev₃ := by
    apply _NDEvent.ext
    case guard =>
      simp
      funext m x
      sorry
    case effect =>
      apply _Effect_ext_ax
      sorry


@[simp]
def arrow_NDEvent (M) [Machine CTX M] (f : α → β) : _NDEvent M α β :=
  {
    effect := fun m x (y, m') => y = f x ∧ m' = m
  }

-- Split is simply parallel composition
@[simp]
def split_NDEvent [Machine CTX M] (ev₁ : _NDEvent M α β) (ev₂ : _NDEvent M γ δ) : _NDEvent M (α × γ) (β × δ) :=
  {
    guard := fun m (x, y) => ev₁.guard m x ∧ ev₂.guard m y
    effect := fun m (x, y) ((x', y'), m') => ev₁.effect m x (x', m') ∧ ev₂.effect m y (y', m')
  }

-- Remark: without an explicit first the law `arrow_unit` is not provable
@[simp]
def first_NDEvent [Machine CTX M] (ev : _NDEvent M α β) : _NDEvent M (α × γ) (β × γ) :=
  {
    guard := fun m (x, _) => ev.guard m x
    effect := fun m (x, y) ((x', y'), m') => ev.effect m x (x', m') ∧ y'= y
  }

-- An alternative possible definition for split based on first

@[simp]
def split_NDEvent_fromFirst [Machine CTX M] (ev₁ : _NDEvent M α β) (ev₂ : _NDEvent M γ δ) : _NDEvent M (α × γ) (β × δ) :=
  Arrow.split_from_first (arrow_NDEvent M (fun (x, y) => (y, x)))
                         first_NDEvent ev₁ ev₂

/-
instance [Machine CTX M]: Arrow (_NDEvent M) where
  arrow := arrow_NDEvent M
  split := split_NDEvent
  first := first_NDEvent
-/

-- a more direct definition
instance [Machine CTX M] [Semigroup M]: Arrow (_NDEvent M) where
  arrow {α β} (f : α → β) : _NDEvent M α β := {
    guard := fun _ _ => True
    effect := fun m x (y, m') => y = f x ∧ m' = m
  }

  split {α α' β β'} (ev₁ : _NDEvent M α β) (ev₂ : _NDEvent M α' β') : _NDEvent M (α × α') (β × β') := {
    guard := fun m (x,y) => ev₁.guard m x ∧ ev₂.guard m y
    effect := fun m (x, y) ((x', y'), m') =>
                ∃ m'₁ m'₂, ev₁.effect m x (x', m'₁) ∧ ev₂.effect m y (y', m'₂) ∧ m' = m'₁ * m'₂
  }
  first := first_NDEvent

instance [Machine CTX M] [Semigroup M]: LawfulArrow (_NDEvent M) where
  arrow_id := by simp [Arrow.arrow]
  arrow_ext f := by simp [Arrow.arrow, Arrow.first]
                    funext m (x, z) ((y, z'), m')
                    simp
                    constructor
                    <;> (intro H ; simp [H])

  arrow_fun f g := by simp [Arrow.arrow]
                      funext m x (z, m')
                      simp
                      constructor
                      · intro H
                        exists (f x)
                        simp [H]
                      · intro Hex
                        cases Hex
                        case _ y H =>
                          simp [H]
  arrow_xcg ev g := by simp [Arrow.arrow, Arrow.first]
                       funext m (x, y₁) ((y₂, x'), m')
                       simp
                       constructor
                       · intro Hex
                         obtain ⟨x'', z, m'₁, ⟨⟨⟨H₁, H₂⟩, H₃⟩, ⟨H₄, H₅⟩⟩⟩ := Hex
                         exists y₂ ; exists y₁
                         simp [*] at *
                         assumption
                       · intro Hex
                         obtain ⟨y₃, y₄, ⟨⟨H₁,H₂,H₂'⟩,H₃,H₄⟩⟩ := Hex
                         exists x ; exists (g y₁) ; exists m
                         simp [*] at *

  arrow_unit ev := by simp [Arrow.arrow, Arrow.first]
                      funext m (x, y₁) (y₂, m')
                      simp
                      constructor
                      · intro Hex
                        exists x
                        exists m
                      · intro Hex
                        obtain ⟨x', Hex⟩  := Hex
                        obtain ⟨m'', ⟨⟨H₁ , H₂⟩, H₃⟩⟩ := Hex
                        rw [H₁, H₂] at H₃
                        assumption

  arrow_assoc ev := by simp [Arrow.arrow, Arrow.first]
                       funext m ((x, z), t) ((y, z', t'), m')
                       simp
                       constructor
                       · intro Hex
                         obtain ⟨y',z'', t'', H⟩ := Hex
                         obtain ⟨⟨⟨H₁, H₂⟩, H₃⟩, ⟨H₄, H₅, H₆⟩⟩ := H
                         simp [*] at *
                         exists x ; exists z ; exists t
                         exists m
                       ·  intro Hex
                          obtain ⟨x',z'',t'', Hex⟩ := Hex
                          obtain ⟨m'', ⟨⟨H₁, H₂⟩, ⟨H₃,H₄,H₅⟩⟩⟩ := Hex
                          simp [*] at *
                          exists y ; exists z ; exists t

/-  Other misc. combinators -/

def dlfNDEvent [Machine CTX M] (ev₁ : _NDEvent M α β) (ev₂ : _NDEvent M α β)
  : _NDEvent M α β :=
  {
    guard := fun m x => ev₁.guard m x ∨ ev₂.guard m x
    effect := fun m x (y, m') =>
      (ev₁.guard m x → ev₁.effect m x (y, m'))
      ∧ (ev₂.guard m x → ev₂.effect m x (y, m'))
  }
