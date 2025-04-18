import Mathlib.Tactic

import LeanMachines.Event.Basic
import LeanMachines.Event.Ordinary
import LeanMachines.Examples.Multiref.Press.Weak_reaction
import LeanMachines.Refinement.Relational.Basic
import LeanMachines.Refinement.Relational.Ordinary

structure SrCtxt where

structure StrongReaction extends WeakReaction where


instance : Machine SrCtxt StrongReaction where
  context := {}
  invariant m :=
    (m.cr ≤ m.ca) -- pat0_5
    ∧ (m.a ∧ ¬ m.r → m.cr < m.ca) -- pat0_6
    ∧ (m.ca ≤ m.cr + 1) -- pat1_1
    ∧ ((¬ m.a ∨ m.r) → m.ca = m.cr) -- pat1_4


instance : Refinement WeakReaction StrongReaction where
  refine wr sr := wr = sr.toWeakReaction
  refine_safe am m :=
    by
      intros hinv href
      rw[href]
      simp[Machine.invariant] at *
      have ⟨hinv₁,hinv₂,_⟩ := hinv
      apply And.intro hinv₁ hinv₂

def StrongReaction.Init :
  SafeInitREvent WeakReaction StrongReaction (WeakReaction.Init) Unit Unit :=
  newInitREvent''
  (WeakReaction.Init)
  {
    init _ := ⟨false,false,0,0⟩
    safety hgrd :=
      by
        simp[Machine.invariant]
    strengthening hgrd :=
      by
        simp[WeakReaction.Init]
    simulation hgrd :=
      by
        simp[Refinement.refine,WeakReaction.Init]
  }

def StrongReaction.Action_on : OrdinaryREvent WeakReaction StrongReaction WeakReaction.Action_on Unit Unit :=
  newREvent''
  WeakReaction.Action_on
  {
    guard := fun m => ¬ m.a ∧ ¬ m.r
    action m _ := ⟨true,m.r,m.ca+1,m.cr⟩
    safety m :=
      by
        simp[Machine.invariant]
        intros pat0_5 pat0_6 pat1_1 pat1_4 hgrd₁ hgrd₂
        constructor
        · omega
        · constructor
          · omega
          · constructor
            · exact Nat.le_of_eq (pat1_4 (Or.inl hgrd₁))
            · intro hmrt
              rw [hmrt] at hgrd₂
              contradiction

    strengthening m hinv :=
      by
        simp[WeakReaction.Action_on,Refinement.refine]
        exact fun a b => a

    simulation m hinv :=
      by
        simp[Refinement.refine,WeakReaction.Action_on]
  }

def StrongReaction.Action_off : OrdinaryREvent WeakReaction StrongReaction WeakReaction.Action_off Unit Unit :=
  newREvent''
  WeakReaction.Action_off
  {
    guard m := m.a ∧ m.r
    action m _ := ⟨false, m.r,m.ca,m.cr⟩
    safety m :=
      by
        simp[Machine.invariant]
        intros _ _ _ pat1_4 hgrd₁ hgrd₂
        constructor
        · assumption
        · constructor
          · assumption
          · exact (pat1_4 (Or.inr hgrd₂))

    strengthening m hinv :=
      by
        simp[Machine.invariant,Refinement.refine,WeakReaction.Action_off]
        exact fun a b => a

    simulation m hinv :=
      by
        simp[Refinement.refine,WeakReaction.Action_off]
  }

def StrongReaction.Reaction_on : OrdinaryREvent WeakReaction StrongReaction WeakReaction.Reaction_on Unit Unit :=
  newREvent''
  WeakReaction.Reaction_on
  {
    guard m := ¬ m.r ∧ m.a
    action m hgrd := ⟨m.a,true,m.ca,m.cr+1⟩
    safety m :=
      by
        simp[Machine.invariant]
        intros pat0_5 pat0_6 pat1_1 pat1_4 hgrd₁ hgrd₂
        constructor
        · have hlt := pat0_6 hgrd₂ hgrd₁
          omega
        constructor
        · omega
        · have hlt := pat0_6 hgrd₂ hgrd₁
          omega
    strengthening m hinv :=
      by
        simp[Machine.invariant,WeakReaction.Reaction_on,Refinement.refine]
    simulation m hinv :=
      by
        simp[Refinement.refine,WeakReaction.Reaction_on]

  }

def StrongReaction.Reaction_off : OrdinaryREvent WeakReaction StrongReaction WeakReaction.Reaction_off Unit Unit :=
  newREvent''
  WeakReaction.Reaction_off
  {
    guard m := m.r ∧ ¬ m.a
    action m _ := ⟨m.a,false,m.ca,m.cr⟩
    safety m :=
      by
        simp[Machine.invariant]
        intros pat0_5 pat0_6 pat1_1 pat1_4 hgrd₁ hgrd₂
        constructor
        · assumption
        constructor
        · intro mat
          rw[mat] at hgrd₂
          contradiction
        constructor
        · assumption
        · intro _
          exact (pat1_4 (Or.inl hgrd₂))
    strengthening m hinv :=
      by
        simp[Machine.invariant,WeakReaction.Reaction_off,Refinement.refine]
    simulation m hinv :=
      by
        simp[Refinement.refine,WeakReaction.Reaction_off]
  }
