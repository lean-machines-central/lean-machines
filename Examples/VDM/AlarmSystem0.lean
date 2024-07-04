import Mathlib.Tactic
import Mathlib.Data.Finset.Basic

import LeanMachines.Event.Basic
import LeanMachines.Event.Ordinary

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

structure ASys0 (ctx : ASys0.Context) where
  experts : Finset Expert

def ASys0.invariant (asys : ASys0 ctx) : Prop :=
  ∀ exp₁ ∈ asys.experts, ∀ exp₂ ∈ asys.experts,
    exp₁ ≠ exp₂ → exp₁.eid ≠ exp₂.eid

@[simp]
def ASys0.reset : ASys0 ctx := { experts := ∅ }

instance: Machine ASys0.Context (ASys0 ctx) where
  context := ctx
  invariant asys := ASys0.invariant asys
  reset := ASys0.reset

def Init : InitEvent (ASys0 ctx) Unit Unit := newInitEvent'' {
  init := ASys0.reset
  safety := by
    intro H ; clear H
    simp [Machine.invariant, ASys0.invariant]
}

def AddExpert : OrdinaryEvent (ASys0 ctx) Expert Unit := newEvent' {
  guard := fun asys exp => ∀ exp' ∈ asys.experts, exp'.eid ≠ exp.eid
  action := fun asys exp => { experts := asys.experts ∪ {exp} }

  safety := fun asys exp => by
    simp [Machine.invariant, ASys0.invariant]
    intros Hinv Hgrd exp₁ Hexp₁ exp₂ Hexp₂ Hneq
    cases Hexp₁
    case inl Hexp₁ =>
      cases Hexp₂
      case inl Hexp₂ =>
        exact Hinv exp₁ Hexp₁ exp₂ Hexp₂ Hneq
      case inr Hexp₂ =>
        rw [Hexp₂] at *
        exact Hgrd exp₁ Hexp₁
    case inr Hexp₁ =>
      cases Hexp₂
      case inl Hexp₂ =>
        rw [Hexp₁] at *
        exact fun a => Hgrd exp₂ Hexp₂ (id (Eq.symm a))
      case inr Hexp₂ =>
        rw [Hexp₁, Hexp₂] at Hneq
        contradiction
}


end AlarmSystem
