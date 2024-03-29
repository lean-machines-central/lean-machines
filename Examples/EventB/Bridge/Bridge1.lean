import Mathlib.Tactic

import Examples.EventB.Bridge.Prelude
import Examples.EventB.Bridge.Bridge0

import EventSystems.Refinement.Basic
import EventSystems.Refinement.Convergent


namespace BridgeSpec

structure Bridge1 (ctx : Context) where
  nbToIsland : Nat
  nbOnIsland : Nat
  nbFromIsland : Nat

@[simp]
def Bridge1.totalCars (b : Bridge1 ctx) := b.1 + b.2 + b.3

@[simp]
def Bridge1.invariant₁ (b : Bridge1 ctx) := b.totalCars ≤ ctx.maxCars

@[simp]
def Bridge1.invariant₂ (b : Bridge1 ctx) := b.nbFromIsland = 0 ∨ b.nbToIsland = 0

instance: Machine Context (Bridge1 ctx) where
  context := ctx
  invariant b := b.invariant₁ ∧ b.invariant₂
  reset := ⟨0, 0, 0⟩

instance: Refinement (Bridge0 ctx) (Bridge1 ctx) where
  refine := fun b0 b1 => b1.totalCars = b0.nbCars
  refine_safe := fun b0 b1 => by simp [Machine.invariant]
                                 intros Hinv₁ _ Href
                                 simp [Hinv₁, ←Href]
  refine_reset := fun b0 => by simp [Machine.reset]
                               intro H ; simp [H]

/- We de not exploit this but this is an interesting property -/
theorem Bridge1.refine_uniq (b1 : Bridge1 ctx) (b0a b0b : Bridge0 ctx):
    Machine.invariant b1
    → Refinement.refine b0a b1 → Refinement.refine (M:=Bridge1 ctx) b0b b1
    → b0a = b0b :=
by
  simp [Machine.invariant, Refinement.refine]
  intros Hinv₁ _ Href Href'
  simp [*] at *
  cases b1
  case mk _ =>
    simp at *
    cases b0b
    case mk nb' =>
      simp at Href
      simp [Href]

namespace Bridge1

def Init : InitREvent (Bridge0 ctx) (Bridge1 ctx) Unit Unit :=
  newInitREvent'' {
    init := ⟨0, 0, 0⟩
    safety := by simp [Machine.invariant]
    abstract := Bridge0.Init
    strengthening := by simp [Bridge0.Init]
    simulation := by simp [Bridge0.Init, Refinement.refine]
  }

def EnterFromMainland : OrdinaryREvent (Bridge0 ctx) (Bridge1 ctx) Unit Unit :=
  newREvent'' {
    guard := fun b1 => b1.totalCars < ctx.maxCars ∧ b1.nbFromIsland = 0
    action := fun b1 => { b1 with nbToIsland := b1.nbToIsland + 1 }
    safety := fun b1 => by simp [Machine.invariant]
                           intros _ _ Hgrd₁ Hgrd₂
                           constructor
                           · simp_arith
                             exact Hgrd₁
                           · assumption
    abstract := Bridge0.EnterFromMainland
    strengthening := fun b1 => by simp [Machine.invariant, Refinement.refine, Bridge0.EnterFromMainland, newEvent']
                                  intros _ _ Hgd₁ _ b0 Href
                                  exact Eq.trans_lt (id Href.symm) Hgd₁
    simulation := fun b1 => by simp [Machine.invariant, Refinement.refine, Bridge0.EnterFromMainland, newEvent']
                               intros _ _ _ _ b0 Href
                               simp_arith
                               exact Href
  }

def LeaveToMainland : OrdinaryREvent (Bridge0 ctx) (Bridge1 ctx) Unit Unit :=
  newREvent'' {
    guard := fun b1 => b1.nbFromIsland > 0
    action := fun b1 => { b1 with nbFromIsland := b1.nbFromIsland - 1 }
    safety := fun b1 => by simp [Machine.invariant]
                           intros Hinv₁ Hinv₂ Hgrd
                           cases Hinv₂
                           case inl Hinv₂ =>
                             linarith
                           case inr Hinv₂ =>
                             simp [Hinv₂]
                             simp [Hinv₂] at Hinv₁
                             rw [← Nat.add_sub_assoc]
                             · simp_arith [Hinv₁]
                               exact Nat.le_step Hinv₁
                             · exact Hgrd
    abstract := Bridge0.LeaveToMainland
    strengthening := fun b1 => by simp [Machine.invariant, Refinement.refine, Bridge0.LeaveToMainland, newEvent']
                                  intros _ _ Hgrd b0 Href
                                  linarith
    simulation := fun b1 => by simp [Machine.invariant, Refinement.refine, Bridge0.LeaveToMainland, newEvent']
                               intros _ _ Hgrd b0 Href
                               rw [← Nat.add_sub_assoc]
                               · rw [←Href]
                               · exact Hgrd
  }


def EnterIsland : ConvergentREvent Nat (Bridge0 ctx) (Bridge1 ctx) Unit Unit :=
  newConcreteREvent'' {
    guard := fun b1 => b1.nbToIsland > 0
    action := fun b1 => ⟨b1.nbToIsland - 1, b1.nbOnIsland + 1, b1.nbFromIsland⟩
    safety := fun b1 => by simp [Machine.invariant]
                           intros Hinv₁ Hinv₂ Hgrd
                           constructor
                           ·  rw [Nat_sub_add_comm_cancel]
                              · assumption
                              · exact Hgrd
                           · cases Hinv₂
                             case right.inl Hinv₂ => exact Or.inl Hinv₂
                             case right.inr Hinv₂ =>
                               apply Or.intro_right
                               simp [Hinv₂]
    variant := fun b1 => b1.nbToIsland
    convergence := fun b1 => by simp [Machine.invariant]
                                intros _ _ Hgrd
                                apply Nat.pred_lt
                                exact Nat.pos_iff_ne_zero.mp Hgrd
    simulation := fun b1 => by simp [Machine.invariant, Refinement.refine]
                               intros _ _ Hgrd b0 Href
                               rw [Nat_sub_add_comm_cancel]
                               · assumption
                               · exact Hgrd
  }


def LeaveIsland : ConvergentREvent Nat (Bridge0 ctx) (Bridge1 ctx) Unit Unit :=
  newConcreteREvent'' {
    guard := fun b1 => b1.nbOnIsland > 0 ∧ b1.nbToIsland = 0
    action := fun b1 => ⟨b1.nbToIsland, b1.nbOnIsland - 1, b1.nbFromIsland + 1⟩
    safety := fun b1 => by simp [Machine.invariant]
                           intros Hinv₁ _ Hgrd₁ Hgrd₂
                           simp [Hgrd₂] at Hinv₁
                           simp [Hgrd₂]
                           have Hgoal : b1.nbOnIsland - 1 + (b1.nbFromIsland + 1)
                                        = b1.nbOnIsland - 1 + 1 + b1.nbFromIsland := by
                             simp_arith
                           rw [Hgoal] ; clear Hgoal
                           rw [Nat.sub_add_cancel Hgrd₁]
                           assumption
    variant := fun b1 => b1.nbOnIsland
    convergence := fun b1 => by simp [Machine.invariant]
                                intros _ _ Hgrd₁ _
                                apply Nat.pred_lt
                                exact Nat.pos_iff_ne_zero.mp Hgrd₁
    simulation := fun b1 => by simp [Machine.invariant, Refinement.refine]
                               intros _ _ Hgrd₁ Hgrd₂ b0 Href
                               simp [Hgrd₂]
                               rw [Nat.add_left_comm]
                               rw [Nat.sub_add_cancel Hgrd₁]
                               simp [Hgrd₂] at Href
                               rw [←Href]
                               simp_arith
  }

theorem deadlockFreedom (m : Bridge1 ctx):
  Machine.invariant m
  → EnterFromMainland.guard m () ∨ LeaveToMainland.guard m ()
    ∨ EnterIsland.guard m () ∨ LeaveIsland.guard m () :=
by
  simp [Machine.invariant, EnterFromMainland, LeaveToMainland, EnterIsland, LeaveIsland]
  intro Hinv₁ Hinv₂
  have Hctx := ctx.maxCars_pos
  cases Hinv₂
  case inl Hinv₂ =>
    simp [Hinv₂] ; simp [Hinv₂] at Hinv₁
    have H₁: m.nbToIsland + m.nbOnIsland < ctx.maxCars
             ∨ m.nbToIsland + m.nbOnIsland = ctx.maxCars := by
      apply Nat.lt_or_eq_of_le
      assumption
    cases H₁
    case inl H₁ => simp [H₁]
    case inr H₁ =>
      apply Or.intro_right
      by_cases m.nbToIsland = 0
      case pos H₂ =>
        simp [H₂]
        simp [H₂] at H₁
        exact Nat.lt_of_lt_of_eq Hctx (id H₁.symm)
      case neg H₂ =>
        apply Or.intro_left
        exact Nat.pos_of_ne_zero H₂
  case inr Hinv₂ =>
    simp [Hinv₂] ; simp [Hinv₂] at Hinv₁
    by_cases m.nbFromIsland = 0
    case pos H₁ =>
      simp [H₁] ; simp [H₁] at Hinv₁
      have H₂: m.nbOnIsland < ctx.maxCars
             ∨ m.nbOnIsland = ctx.maxCars := by
        apply Nat.lt_or_eq_of_le
        assumption
      cases H₂
      case inl H₂ => simp [H₂]
      case inr H₂ =>
        apply Or.intro_right
        exact Nat.lt_of_lt_of_eq Hctx (id H₂.symm)
    case neg H₁ =>
      simp [H₁]
      left
      exact Nat.pos_of_ne_zero H₁

  done

end Bridge1

end BridgeSpec
