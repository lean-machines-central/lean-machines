
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
structure _NDEvent (M) [Machine CTX M] (α) (β : Type)
  extends _EventRoot M α where

  effect: M → α → (β × M) → Prop

theorem _NDEvent.ext [Machine CTX M] (ev₁ : _NDEvent M α β) (ev₂ : _NDEvent M α β):
  ev₁.to_EventRoot = ev₂.to_EventRoot
  → ev₁.effect = ev₂.effect
  → ev₁ = ev₂ :=
by
  intros H₁ H₂
  cases ev₁
  case mk _evr₁ _eff₁ =>
    cases ev₂
    case mk _evr₃ _eff₂ =>
      simp [*] at *
      simp [H₁, H₂]

@[simp]
def _Event.to_NDEvent [Machine CTX M] (ev : _Event M α β) : _NDEvent M α β :=
{
  guard := ev.guard
  effect := fun m x (x'', m'') => let (x', m') := ev.action m x
                                  m'' = m' ∧ x'' = x'
}

/-- The internal representation of *non-deterministic* initialization events
with: `M` the machine type,
`α` the input type, and `β` the output type of the event
.-/
structure _InitNDEvent (M) [Machine CTX M] (α) (β : Type) where
  guard: α → Prop
  init: α → (β × M) → Prop

@[simp]
def _InitEvent.to_InitNDEvent [Machine CTX M] (ev : _InitEvent M α β) : _InitNDEvent M α β :=
{
  guard := ev.guard
  init := fun x (x'', m'') => let (x', m') := ev.init x
                              m'' = m' ∧ x'' = x'
}

@[simp]
def _InitNDEvent.to_NDEvent [Machine CTX M] (ev : _InitNDEvent M α β) : _NDEvent M α β :=
{
  guard := fun m x => m = Machine.reset ∧ ev.guard x
  effect := fun _ x (y, m') => ev.init x (y, m')
}

@[simp]
def skip_NDEvent [Machine CTX M] : _NDEvent M α β :=
  {
    effect := fun m _ (_, m') => m' = m
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
    effect := fun m x (y, m') => ∃ z, ∃ m'', ev.effect m x (z, m'')
                                             ∧ y = f z ∧ m' = m''
  }

instance [Machine CTX M] : LawfulFunctor (_NDEvent M γ) where
  map_const := rfl
  id_map ev := by simp [Functor.map]

  comp_map g h ev := by simp [Functor.map]
                        funext m x (y,m')
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
    effect := fun m x (y, m') => ev.effect m x ((f y), m')
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
     effect := fun m x (y, m')  => ev.effect m (f x) (y, m')
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
  dimap_comp f f' g g' := by simp [Profunctor.dimap, ContravariantFunctor.contramap, Functor.map]
                             funext ev
                             simp
                             funext m x (y,m')
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
      effect := fun m (x,u) ((y, v), m') => v = u ∧ ev.effect m x (y, m')
    }

instance [Machine CTX M] : LawfulStrongProfunctor (_NDEvent M) where


instance [Machine CTX M]: Category (_NDEvent M) where
  id := {
    effect := fun m x (y, m') => y = x ∧ m' = m
  }

  comp {α β γ} (ev₂ : _NDEvent M β γ) (ev₁ : _NDEvent M α β) : _NDEvent M α γ :=
    { guard := fun m x => ev₁.guard m x ∧ (∀ y, ∀ m', ev₁.effect m x (y, m')
                                           → ev₂.guard m' y)
      effect := fun m x (z, m'') => ∃ y, ∃ m', ev₁.effect m x (y, m') ∧ ev₂.effect m' y (z, m'')
    }

instance [Machine CTX M]: LawfulCategory (_NDEvent M) where
  id_right ev := by cases ev
                    case mk evr eff =>
                      simp
                      funext m x (z, m'')
                      simp
                      constructor
                      · intros Heff
                        cases Heff
                        case _ y Heff =>
                          cases Heff
                          case _ m' Heff =>
                            cases Heff
                            case _ Heq Heff =>
                              simp [Heq] at Heff
                              assumption
                      intro Heff
                      exists x
                      exists m

  id_left ev := by cases ev
                   case mk evr eff =>
                     simp


  id_assoc ev₁ ev₂ ev₃ := by
    cases ev₁
    case mk evr₁ eff₁ =>
      cases ev₂
      case mk evr₂ eff₂ =>
        cases ev₃
        case mk evr₃ eff₃ =>
          simp
          constructor
          case left =>
            funext m x
            case h.h =>
              simp
              constructor
              case mpr =>
                intros H₁
                cases H₁
                case intro Hgrd₃ H₁ =>
                  constructor
                  case left =>
                    simp [Hgrd₃]
                    intros y m' Heff₃
                    apply (H₁ y m' Heff₃).left
                  case right =>
                    intros z m'' y m' Heff₃ Heff₂
                    have H₁' := H₁ y m' Heff₃  ; clear H₁
                    cases H₁'
                    case intro Hgrd₂ Hgrd₁ =>
                      apply Hgrd₁ z m''
                      assumption
              case mp =>
                  simp
                  intros Hgrd₃ Hgrd₂ Hgrd₁
                  constructor
                  case left =>
                    assumption
                  case right =>
                    intros y m' Heff₃
                    constructor
                    case left =>
                      apply Hgrd₂
                      assumption
                    case right =>
                      intros z m'' Heff₂
                      apply Hgrd₁ z m'' <;> assumption
          case right =>
            funext m x (t, m₃)
            case h.h.h =>
              simp
              constructor
              case mp =>
                intro Hex
                cases Hex
                case intro z Hex =>
                  cases Hex
                  case intro m'' Hex =>
                  cases Hex
                  case intro Hex Heff₁ =>
                    cases Hex
                    case intro y Hex =>
                      cases Hex
                      case intro m' Heff =>
                        exists y
                        exists m'
                        simp [Heff]
                        exists z
                        exists m''
                        simp [Heff₁, Heff]
              case mpr =>
                intro Hex
                cases Hex
                case intro y Hex =>
                  cases Hex
                  case intro m' Hex =>
                    cases Hex
                    case intro Heff₃ Hex =>
                      cases Hex
                      case intro z Hex =>
                        cases Hex
                        case intro m'' Heff =>
                          exists z
                          exists m''
                          constructor
                          case left =>
                            exists y
                            exists m'
                            simp [Heff₃, Heff]
                          case right =>
                            simp [Heff]




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
