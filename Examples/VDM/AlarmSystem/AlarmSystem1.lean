
import Examples.VDM.AlarmSystem.AlarmSystem0

import LeanMachines.Refinement.Strong.Basic
import LeanMachines.Refinement.Strong.Abstract
import LeanMachines.Refinement.Strong.Concrete

namespace AlarmSystem

structure Period where
  id : Nat
  deriving Repr, DecidableEq, Ord

instance: LE Period := Ord.toLE inferInstance

structure ASys1.Context extends ASys0.Context where
  maxPeriods : Nat
  deriving Repr

structure ASys1 (ctx : ASys1.Context) extends ASys0 ctx.toContext where
  schedule : Period → Finset Expert

@[simp]
def ASys1.invariant₁ (asys : ASys1 ctx) :=
  Machine.invariant asys.toASys0

def ASys1.invariant₂ (asys : ASys1 ctx) :=
  ∀ per, asys.schedule per ⊆ asys.experts

def ASys1.invariant₃ (asys : ASys1 ctx) :=
  ∀ per, asys.schedule per ≠ ∅ → per.id ≤ ctx.maxPeriods

instance: Machine ASys1.Context (ASys1 ctx) where
  context := ctx
  invariant asys := ASys1.invariant₁ asys ∧ ASys1.invariant₂ asys ∧ ASys1.invariant₃ asys
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
    , ASys1.invariant₃, ASys0.invariant₁, ASys0.invariant₂]
}

theorem superposition (asys : ASys1 ctx):
  Machine.invariant asys.toASys0
  → invariant₂ asys
  → invariant₃ asys
  → Machine.invariant asys :=
by
  simp [Machine.invariant] ; intros ; simp [*]

def AddExpert : ConvergentREvent Nat (ASys0 ctx.toContext) (ASys1 ctx) Expert Unit := newAbstractConvergentSREvent' ASys0.AddExpert {
  step_inv := fun asys exp => by
    simp [FRefinement.lift, SRefinement.unlift]
    intros Hinv Hgrd
    have Hainv : Machine.invariant asys.toASys0 := by
      exact Refinement.refine_safe asys.toASys0 asys Hinv rfl
    have Hsafe := ASys0.AddExpert.po.safety asys.toASys0 exp Hainv Hgrd
    obtain ⟨_, Hinv₂, Hinv₃⟩ := Hinv
    simp [ASys0.AddExpert] at *
    apply superposition
    · exact Hsafe
    · intro per
      apply subset_trans (b:=asys.experts)
      · simp
        exact Hinv₂ per
      · simp
        exact Finset.subset_union_left
    -- next
    simp [ASys1.invariant₃] at *
    exact fun per a => Hinv₃ per a
  }

namespace AssignExpert

@[simp]
def guard₁ (_ : ASys1 ctx) (per : Period) : Prop :=
  per.id ≤ ctx.maxPeriods

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

def AssignExpert : OrdinaryRDetEvent (ASys0 ctx.toContext) (ASys1 ctx) (Period × Expert) Unit :=
newConcreteSREvent' {
  guard := fun asys (per, exp) => AssignExpert.guard₁ asys per
                                  ∧ AssignExpert.guard₂ asys exp
                                  ∧ AssignExpert.guard₃ asys per exp
  action := fun asys (per, exp) => AssignExpert.action asys per exp

  safety := fun asys (per, exp) => by
    simp [Machine.invariant]
    intros Hinv₁ Hinv₂ Hinv₃ Hinv₄ Hgrd₁ Hgrd₂ _
    constructor
    · exact ⟨Hinv₁, Hinv₂⟩
    constructor
    · simp [ASys1.invariant₂] at *
      intro per'
      split
      case _ Heq =>
        have Hinv₃ := Hinv₃ per
        refine Finset.union_subset_iff.mpr ?_
        constructor
        · assumption
        · exact Finset.singleton_subset_iff.mpr Hgrd₂
      case _ Nheq =>
        exact Hinv₃ per'
    -- next
    simp [ASys1.invariant₃] at *
    intro per'
    split
    case _ Heq =>
      intro _
      exact le_of_eq_of_le (congrArg Period.id Heq) Hgrd₁
    case _ Hneq =>
      intro Hper'
      exact Hinv₄ per' Hper'

  simulation := fun asys (per, exp) => by
    simp [Machine.invariant, FRefinement.lift]

  -- Remark : it would be rather limiting to enforce this
  --          concrete event to be convergent
  --          (cf. Event-B book about introducing concrete events)

}

end ASys1

end AlarmSystem
