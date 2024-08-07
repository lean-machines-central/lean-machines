
import Examples.VDM.AlarmSystem.AlarmSystem1

import LeanMachines.Refinement.Strong.Basic
import LeanMachines.Refinement.Strong.Abstract
import LeanMachines.Refinement.Strong.Concrete

namespace AlarmSystem

structure Alarm where
  period : Period
  quali : Qualification
  deriving DecidableEq

structure ASys2 (ctx : ASys1.Context) extends ASys1 ctx where
  alarms : List Alarm

@[simp]
def ASys2.invariant₁ (asys : ASys2 ctx) := Machine.invariant asys.toASys1

def ASys2.invariant₂ (asys : ASys2 ctx) :=
  ∀ alarm ∈ asys.alarms, ∃ exp ∈ asys.schedule alarm.period, exp.quali = alarm.quali

instance: Machine ASys1.Context (ASys2 ctx) where
  context := ctx
  invariant asys := ASys2.invariant₁ asys ∧ ASys2.invariant₂ asys
  reset := { toASys1 := Machine.reset
             alarms := [] }

instance: SRefinement  (ASys1 ctx) (ASys2 ctx) where
  lift asys := asys.toASys1
  lift_safe asys := by
    simp [Machine.invariant] ; intros ; simp [*]

  unlift asys2 asys1' := { toASys1 := asys1'
                           alarms := asys2.alarms }

  lift_unlift asys2 asys1' := by simp
  lu_reset asys1' := by simp

namespace ASys2

def Init : InitEvent (ASys2 ctx) Unit Unit := newInitEvent'' {
  init := Machine.reset
  safety := by
    intro H ; clear H
    simp [Machine.reset, Machine.invariant
         , ASys0.invariant₁, ASys0.invariant₂, ASys1.invariant₂, ASys1.invariant₃
         , ASys2.invariant₂]
}

theorem superposition (asys : ASys2 ctx):
  Machine.invariant asys.toASys1
  → invariant₂ asys
  → Machine.invariant asys :=
by
  cases asys
  case mk _toASys1 _alarms =>
    simp
    intros Hainv Hinv₅
    simp [Machine.invariant] at *
    simp [*]

def AddExpert : ConvergentREvent Nat (ASys1 ctx) (ASys2 ctx) Expert Unit :=
  newAbstractConvergentSREvent' ASys1.AddExpert.toConvergentEvent {
    step_inv := fun asys exp => by
      simp [FRefinement.lift, SRefinement.unlift]
      intro Hinv Hgrd
      have Hainv : Machine.invariant asys.toASys1 := by
        exact Refinement.refine_safe asys.toASys1 asys Hinv rfl
      have HSafe := ASys1.AddExpert.po.safety asys.toASys1 exp Hainv Hgrd
      apply superposition
      · exact HSafe
      -- next
      obtain ⟨_, Hinv₂⟩ := Hinv
      simp [ASys2.invariant₂] at *
      simp [ASys1.AddExpert, SRefinement.unlift]
      intros alarm Halarm
      exact Hinv₂ alarm Halarm
}

def RaiseAlarm : OrdinaryRDetEvent (ASys1 ctx) (ASys2 ctx) Alarm Unit :=
  newConcreteSREvent' {
    guard := fun asys alarm =>
               ∃ exp ∈ asys.schedule alarm.period, exp.quali = alarm.quali
    action := fun asys alarm => { asys with alarms := alarm :: asys.alarms }

    safety := fun asys alarm => by
      intro Hinv
      obtain ⟨⟨⟨Haainv₁, Haainv₂⟩, Hainv₂, Hainv₃⟩, Hinv₂⟩ := Hinv
      simp
      intros exp Hgrd₁ Hgrd₂
      simp [Machine.invariant]
      simp [*, ASys2.invariant₂]
      constructor
      · exists exp
      intros alarm' Halarm'
      exact Hinv₂ alarm' Halarm'

    simulation := fun asys alarm => by
      intros ; simp [FRefinement.lift]

  }
