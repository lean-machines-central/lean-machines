import Mathlib.Tactic

import LeanMachines.Event.Basic
import LeanMachines.Event.Ordinary


structure WrCtxt where


structure WeakReaction where
  a : Bool
  r : Bool
  ca : Nat
  cr : Nat


instance : Machine WrCtxt WeakReaction where
  context := {}
  invariant m :=
    (m.cr ≤ m.ca)                 -- pat0_5
    ∧ (m.a ∧ ¬ m.r → m.cr < m.ca) -- pat0_6

def WeakReaction.Init : InitEvent WeakReaction Unit Unit :=
  newInitEvent''
  {
    init _ := ⟨false,false,0,0⟩
    safety hgrd :=
      by
        simp
        simp[Machine.invariant]
  }


def WeakReaction.Action_on : OrdinaryEvent WeakReaction Unit Unit :=
  newEvent''
  {
    guard := fun m => ¬ m.a
    action m _ := ⟨true,m.r,m.ca+1,m.cr⟩
    safety m :=
      by
        simp[Machine.invariant]
        intros hinv₁ hinv₂ hgrd
        constructor
        · omega
        · intro _
          omega
  }


def WeakReaction.Action_off : OrdinaryEvent WeakReaction Unit Unit :=
  newEvent''
  {
    action m _ := ⟨false, m.r,m.ca,m.cr⟩
    guard m := m.a
    safety m :=
      by
        simp[Machine.invariant]
        intros
        assumption
  }

def WeakReaction.Reaction_on : OrdinaryEvent WeakReaction Unit Unit :=
  newEvent''
  {
    guard m := ¬m.r ∧ m.a
    action m _ := ⟨m.a,true,m.ca,m.cr+1⟩
    safety m  :=
      by
        simp[Machine.invariant]
        intros hinv₁ hinv₂ hgrd₁ hgrd₂
        have hlt := hinv₂ hgrd₂ hgrd₁
        omega

  }

def WeakReaction.Reaction_off : OrdinaryEvent WeakReaction Unit Unit :=
  newEvent''
  {
    guard m := m.r ∧ ¬ m.a
    action m _ := ⟨m.a,false,m.ca,m.cr⟩
    safety m :=
      by
        simp[Machine.invariant]
        intros _ _ _ hgrd₂
        constructor
        · assumption
        · intro h
          rw[h] at hgrd₂
          exfalso
          exact (Bool.eq_not_self true).mp hgrd₂
  }
