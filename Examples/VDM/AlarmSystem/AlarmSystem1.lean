
import Examples.VDM.AlarmSystem.AlarmSystem0

import LeanMachines.Refinement.Strong.Basic
import LeanMachines.Refinement.Strong.Abstract
import LeanMachines.Refinement.Strong.Concrete

namespace AlarmSystem

structure Period where
  pid : Nat
  deriving Repr, DecidableEq, Ord

instance: LE Period := Ord.toLE inferInstance

structure ASys1.Context extends ASys0.Context where
  maxPeriods : Nat
  deriving Repr

structure ASys1 (ctx : ASys1.Context) extends ASys0 ctx.toContext where
  schedule : Period → Finset Expert

@[simp]
def ASys1.invariant₁ (asys : ASys1 ctx) := ASys0.invariant₁ asys.toASys0

def ASys1.invariant₂ (asys : ASys1 ctx) := ASys0.invariant₂ asys.toASys0

def ASys1.invariant₃ (asys : ASys1 ctx) :=
  ∀ per, asys.schedule per ⊆ asys.experts

def ASys1.invariant₄ (asys : ASys1 ctx) :=
  ∀ per, asys.schedule per ≠ ∅ → per.pid ≤ ctx.maxPeriods

instance: Machine ASys1.Context (ASys1 ctx) where
  context := ctx
  invariant asys := ASys1.invariant₁ asys ∧ ASys1.invariant₂ asys ∧ ASys1.invariant₃ asys ∧ ASys1.invariant₄ asys
  reset := { toASys0 := ASys0.reset
             schedule := fun _ => ∅}

instance: SRefinement  (ASys0 ctx.toContext) (ASys1 ctx) where
  lift asys := asys.toASys0
  lift_safe asys := by
    simp [Machine.invariant, ASys1.invariant₁, ASys1.invariant₂]
    intros Hinv₁ Hinv₂ _ _
    exact ⟨Hinv₁, Hinv₂⟩

  unlift asys1 asys0' := { experts := asys0'.experts
                           schedule := asys1.schedule }
  lift_unlift asys1 asys0' := by simp
  lu_reset asys0' := by simp

namespace ASys1

def Init : InitEvent (ASys1 ctx) Unit Unit := newInitEvent'' {
  init := Machine.reset
  safety := by
    intro H ; clear H
    simp [Machine.reset, Machine.invariant, ASys1.invariant₁, ASys1.invariant₂
    , ASys1.invariant₃, ASys1.invariant₄, ASys0.invariant₁, ASys0.invariant₂]
}

def AddExpert : ConvergentREvent Nat (ASys0 ctx.toContext) (ASys1 ctx) Expert Unit := newAbstractConvergentSREvent' ASys0.AddExpert {
  step_inv := fun asys exp => by
    have Hsafe := ASys0.AddExpert.po.safety asys.toASys0 exp
    simp [Machine.invariant, ASys0.AddExpert, FRefinement.lift, SRefinement.unlift] at *
    intros Hinv₁ Hinv₂ Hinv₃ Hinv₄ Hgrd₁ Hgrd₂ Hgrd₃
    have Hsafe' := Hsafe Hinv₁ Hinv₂ Hgrd₁ Hgrd₂ Hgrd₃ ; clear Hsafe
    obtain ⟨Hsafe₁, Hsafe₂⟩ := Hsafe'
    constructor
    · exact Hsafe₁
    constructor
    · exact Hsafe₂
    constructor
    · simp [ASys1.invariant₃] at *
      intro per
      apply subset_trans (b:=asys.experts)
      · exact Hinv₃ per
      · exact Finset.subset_union_left asys.experts {exp}
    -- next
    simp [ASys1.invariant₄] at *
    exact fun per a => Hinv₄ per a
    }

namespace AssignExpert

@[simp]
def guard₁ (_ : ASys1 ctx) (per : Period) : Prop :=
  per.pid ≤ ctx.maxPeriods

@[simp]
def guard₂ (asys : ASys1 ctx) (exp : Expert) : Prop :=
  exp ∈ asys.experts

@[simp]
def guard₃ (asys : ASys1 ctx) (per : Period) (exp : Expert) : Prop :=
  exp ∉ asys.schedule per

@[simp]
def action (asys : ASys1 ctx) (per : Period) (exp : Expert) : ASys1 ctx := {
  experts := asys.experts
  schedule := fun per' => if per' = per
                          then (asys.schedule per) ∪ {exp}
                          else asys.schedule per'
}

end AssignExpert

def AssignExpert : ConvergentRDetEvent Nat (ASys0 ctx.toContext) (ASys1 ctx) (Period × Expert) Unit := newConcreteSREvent' {
  guard := fun asys (per, exp) => AssignExpert.guard₁ asys per
                                  ∧ AssignExpert.guard₂ asys exp
                                  ∧ AssignExpert.guard₃ asys per exp
  action := fun asys (per, exp) => AssignExpert.action asys per exp

  safety := fun asys (per, exp) => by
    simp [Machine.invariant]
    intros Hinv₁ Hinv₂ Hinv₃ Hinv₄ Hgrd₁ Hgrd₂ Hgrd₃
    constructor
    · exact Hinv₁
    constructor
    · exact Hinv₂
    constructor
    · simp [ASys1.invariant₃] at *
      intro per'
      split
      case _ Heq =>
        refine Finset.union_subset_iff.mpr ?_
        constructor
        · exact Hinv₃ per
        · exact Finset.singleton_subset_iff.mpr Hgrd₂
      case _ Heq =>
        exact Hinv₃ per'
    · simp [ASys1.invariant₄] at *
      intro per'
      split
      case _ Heq =>
        intro Hne
        exact le_of_eq_of_le (congrArg Period.pid Heq) Hgrd₁
      case _ Hneq =>
        intro Hne
        exact Hinv₄ per' Hne

  simulation := fun asys (per, exp) => by
    simp [Machine.invariant, FRefinement.lift]

  -- TODO/Question : how can this be convergent ?

}

end ASys1

end AlarmSystem
