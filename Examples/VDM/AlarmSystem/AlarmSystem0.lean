import Mathlib.Tactic
import Mathlib.Data.Finset.Basic

import LeanMachines.Event.Basic
import LeanMachines.Event.Ordinary
import LeanMachines.Event.Convergent

import Examples.VDM.Prelude


namespace AlarmSystem

inductive Qualification :=
| Elec | Mech | Bio | Chem
  deriving Repr, DecidableEq

abbrev ExpertId := Nat

structure Expert where
  eid : ExpertId
  quali : Qualification
  deriving Repr, DecidableEq

structure ASys0.Context where
  maxExperts : Nat
  maxExperts_prop : maxExperts > 0
  deriving Repr

structure ASys0 (ctx : ASys0.Context) where
  experts : Finset Expert

def ASys0.invariant₁ (asys : ASys0 ctx) : Prop :=
  asys.experts.card ≤ ctx.maxExperts

def ASys0.invariant₂ (asys : ASys0 ctx) : Prop :=
  ∀ exp₁ ∈ asys.experts, ∀ exp₂ ∈ asys.experts,
    exp₁ ≠ exp₂ → exp₁.eid ≠ exp₂.eid

@[simp]
def ASys0.reset : ASys0 ctx := { experts := ∅ }

instance: Machine ASys0.Context (ASys0 ctx) where
  context := ctx
  invariant asys := ASys0.invariant₁ asys ∧ ASys0.invariant₂ asys
  reset := ASys0.reset

namespace ASys0

def Init : InitEvent (ASys0 ctx) Unit Unit := newInitEvent'' {
  init := ASys0.reset
  safety := by
    intro H ; clear H
    simp [Machine.invariant, ASys0.invariant₁, ASys0.invariant₂]
}

def AddExpert : ConvergentEvent Nat (ASys0 ctx) Expert Unit := newConvergentEvent' {
  guard := fun asys exp => exp ∉ asys.experts ∧ asys.experts.card < ctx.maxExperts ∧ ∀ exp' ∈ asys.experts, exp'.eid ≠ exp.eid
  action := fun asys exp => { experts := asys.experts ∪ {exp} }

  safety := fun asys exp => by
    simp [Machine.invariant]
    intros _ Hinv₂ _ Hgrd₂ Hgrd₃
    constructor
    case left =>
      simp [ASys0.invariant₁] at *
      have Hcard := Finset.card_union_le asys.experts {exp}
      simp at Hcard
      exact Nat.le_trans Hcard Hgrd₂
    case right =>
      simp [ASys0.invariant₂] at *
      intros exp1 Hexp₁ exp₂ Hexp₂ Hneq
      cases Hexp₁
      case inl Hexp₁ =>
        cases Hexp₂
        case inl Hexp₂ =>
          exact Hinv₂ exp1 Hexp₁ exp₂ Hexp₂ Hneq
        case inr Hexp₂ =>
          rw [Hexp₂] at *
          exact Hgrd₃ exp1 Hexp₁
      case inr Hexp₁ =>
        cases Hexp₂
        case inl Hexp₂ =>
          rw [Hexp₁] at *
          exact fun a => Hgrd₃ exp₂ Hexp₂ (id (Eq.symm a))
        case inr Hexp₂ =>
          rw [Hexp₁, Hexp₂] at Hneq
          contradiction

  variant := fun (asys : ASys0 ctx) => ctx.maxExperts - asys.experts.card

  convergence := fun asys exp => by
    simp [Machine.invariant]
    intros _ _ Hgrd₁ Hgrd₂ Hgrd₃
    refine Nat.sub_lt_sub_left Hgrd₂ ?_ -- apply?
    refine Finset.card_lt_card ?h -- apply?
    refine Finset.ssubset_iff_subset_ne.mpr ?h.a -- apply?
    constructor
    · exact Finset.subset_union_left
    · intro Hcontra
      rw [Hcontra] at Hgrd₁
      have Hin: exp ∈ asys.experts ∪ {exp} := by
        refine Finset.mem_union_right asys.experts ?hh -- apply?
        exact Finset.mem_singleton.mpr rfl -- apply?
      contradiction
}

end ASys0

end AlarmSystem
