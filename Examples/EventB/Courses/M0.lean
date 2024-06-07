import Mathlib.Tactic

import LeanMachines.Event.Basic
import LeanMachines.Event.Ordinary
import LeanMachines.Event.Convergent
import LeanMachines.NonDet.Ordinary

import Examples.EventB.Courses.Prelude

namespace CoursesSpec

structure M0.Context where
  availableCourses : Finset Course
  maxOpenedCourses : Nat
  maxCourses_prop₁ : maxOpenedCourses > 0
  maxCourses_prop₂: maxOpenedCourses ≤ availableCourses.card

structure M0 (ctx : M0.Context) where
  openedCourses : Finset Course

theorem M0.Context_available_courses_Nonempty (ctx : M0.Context):
  ctx.availableCourses ≠ ∅ :=
by
  have H₁ := ctx.maxCourses_prop₁
  have H₂ := ctx.maxCourses_prop₂
  intro Hcontra
  have Hcontra' : ctx.availableCourses.card = 0 := by exact Finset.card_eq_zero.mpr Hcontra
  linarith

def M0.invariant₁ (m : M0 ctx) :=
  m.openedCourses ⊆ ctx.availableCourses

theorem openedCourse_card (m : M0 ctx):
  M0.invariant₁ m
  → m.openedCourses.card ≤ ctx.availableCourses.card :=
by
  apply  Finset.card_le_card

def M0.invariant₂ (m : M0 ctx)  :=
  m.openedCourses.card ≤  ctx.maxOpenedCourses

@[simp]
def M0.reset (ctx : M0.Context) : M0 ctx:= {openedCourses := ∅}

instance: Machine M0.Context (M0 ctx) where
  context := ctx
  invariant m := M0.invariant₁ m ∧ M0.invariant₂ m
  reset := M0.reset ctx

namespace M0

namespace Init

@[simp]
def init : M0 ctx := {openedCourses := ∅}

theorem PO_safety₁:
  @invariant₁ ctx init :=
by
  simp [invariant₁]

theorem PO_safety₂:
  @invariant₂ ctx init :=
by
  simp [invariant₂]

end Init

def Init : InitEvent (M0 ctx) Unit Unit := newInitEvent'' {
  init := Init.init
  safety := by simp [Machine.invariant, M0.invariant₁, M0.invariant₂, Init.PO_safety₁, Init.PO_safety₂]
}

namespace OpenCourses

@[simp]
def guard (m : M0 ctx) := m.openedCourses.card ≠ ctx.maxOpenedCourses

theorem guard_lemma (m : M0 ctx):
  invariant₁ m → invariant₂ m
  → guard m
  → m.openedCourses.card ≠ ctx.availableCourses.card :=
by
  simp [invariant₁, invariant₂]
  intros Hinv₁ Hinv₂ Hgrd
  have Hctx₂ := ctx.maxCourses_prop₂
  have H₁ := Finset.card_le_card Hinv₁
  intro Hcontra
  simp [Hcontra] at * ; clear H₁ Hcontra
  have Hcontra: Finset.card ctx.availableCourses = ctx.maxOpenedCourses := by
    apply le_antisymm <;> assumption
  contradiction

theorem guard_thm (m : M0 ctx):
  invariant₁ m → invariant₂ m
  → guard m
  → m.openedCourses ≠ ctx.availableCourses :=
by
  intros Hinv₁ Hinv₂ Hgrd Heq
  have H₁: m.openedCourses.card = ctx.availableCourses.card := by
    simp [Heq]
  have H₂: m.openedCourses.card ≠ ctx.availableCourses.card := by
    apply guard_lemma <;> assumption
  contradiction

@[simp]
def effect (m m' : M0 ctx) :=
  ∃ cs : Finset Course, cs ⊆ ctx.availableCourses
    ∧ cs ≠ ∅
    ∧ m'.openedCourses = m.openedCourses ∪ cs
    ∧ m'.openedCourses.card ≤ ctx.maxOpenedCourses

theorem PO_safety₁ (m : M0 ctx):
  invariant₁ m
  → ∀m', effect m m' → invariant₁ m' :=
by
  simp [invariant₁, invariant₂]
  intros Hinv₁ m' cs Hact₁ _ Hact₃ _
  simp [Hact₃]
  exact Finset.union_subset Hinv₁ Hact₁

theorem PO_safety₂ (m : M0 ctx):
  invariant₂ m → guard m
  → ∀m', effect m m' → invariant₂ m' :=
by
  simp [invariant₂]

theorem PO_Feasibility (m : M0 ctx):
  invariant₂ m → guard m
  → ∃ m', effect m m' :=
by
  simp [invariant₁, invariant₂]
  intros Hinv₂ Hgrd
  have Hctx₁ := ctx.maxCourses_prop₁
  have Hex: ∃ c, c ∈ ctx.availableCourses := by
    apply Finset_nonempty_ex
    apply M0.Context_available_courses_Nonempty
  cases Hex
  case intro c Hc =>
    exists { openedCourses := m.openedCourses ∪ {c}}
    exists {c}
    constructor
    · simp [Hc]
    · constructor
      · exact Finset.singleton_ne_empty c
      constructor
      · simp
      · have H₁ : Finset.card (m.openedCourses ∪ {c}) ≤ m.openedCourses.card + Finset.card {c} := by
          exact Finset.card_union_le m.openedCourses {c}
        simp at H₁
        have H₂: Finset.card m.openedCourses + 1 ≤ ctx.maxOpenedCourses := by
          apply Nat.add_le_of_le_sub
          · apply Hctx₁
          · apply Nat.le_pred_of_lt
            · exact Nat.lt_of_le_of_ne Hinv₂ Hgrd
        exact Nat.le_trans H₁ H₂

end OpenCourses

def OpenCourses : OrdinaryNDEvent (M0 ctx) Unit Unit := newNDEvent'' {
  guard := OpenCourses.guard
  effect := OpenCourses.effect
  safety := fun m => by simp [Machine.invariant, -OpenCourses.guard, -OpenCourses.effect]
                        intros Hinv₁ Hinv₂ Hgrd m' Hact
                        constructor
                        · apply OpenCourses.PO_safety₁ <;> assumption
                        · apply OpenCourses.PO_safety₂ <;> assumption
  feasibility := fun m => by simp [Machine.invariant]
                             intros
                             apply OpenCourses.PO_Feasibility <;> assumption
}

namespace CloseCourses

@[simp]
def guard (m : M0 ctx) (cs : Finset Course) :=
  cs ⊆ m.openedCourses ∧ cs ≠ ∅

@[simp]
def action (m : M0 ctx) (cs : Finset Course) : M0 ctx :=
  { openedCourses := m.openedCourses \ cs}

theorem PO_safety₁ (m : M0 ctx) (cs : Finset Course):
  invariant₁ m
  → invariant₁ (action m cs) :=
by
  simp [invariant₁]
  intros Hinv₁
  have H₁ : m.openedCourses \ cs ⊆ m.openedCourses := by
    apply Finset.sdiff_subset
  exact Finset.Subset.trans H₁ Hinv₁

theorem PO_safety₂ (cs : Finset Course) (m : M0 ctx):
  invariant₂ m
  → invariant₂ (action m cs) :=
by
  simp [invariant₂]
  intros Hinv₂
  have H₁ : (m.openedCourses \ cs).card ≤ m.openedCourses.card := by
    apply Finset_le_sdiff_sub
  apply le_trans (b:=Finset.card m.openedCourses) <;> assumption

@[local simp]
def variant (m : M0 ctx) := m.openedCourses.card

theorem PO_nonIncreasing (m : M0 ctx) (cs : Finset Course):
  variant (action m cs) ≤ variant m :=
by
  simp
  apply Finset_le_sdiff_sub

theorem PO_convergence (m : M0 ctx) (cs : Finset Course):
  guard m cs
  → variant (action m cs) < variant m :=
by
  simp
  intros Hgrd₁ Hgrd₂
  have Hgrd₁': cs.card ≤ m.openedCourses.card := by
    exact Finset.card_le_card Hgrd₁

  have H₁ := PO_nonIncreasing m cs ; simp at H₁
  apply lt_of_le_of_ne
  · assumption
  · intro Hcontra
    rw [Finset.card_sdiff] at Hcontra
    · have H₂: cs.card ≠ 0 := by
          intro Hzero
          have H₂ : cs = ∅ := by apply Finset.card_eq_zero.1 ; assumption
          contradiction
      have H₃ : cs.card = 0 := by
        apply Nat_sub_zero (a:=m.openedCourses.card)
        · have H₂' : 0 < cs.card := by exact Nat.pos_of_ne_zero H₂
          exact Nat.lt_of_lt_of_le H₂' Hgrd₁'
        · assumption
      contradiction
    · assumption

end CloseCourses

def CloseCourses : ConvergentEvent Nat (M0 ctx) (Finset Course) Unit := newConvergentEvent' {
  guard := CloseCourses.guard
  action := CloseCourses.action
  safety := fun m => by simp [Machine.invariant, -CloseCourses.guard, -CloseCourses.action]
                        intros Hinv₁ Hinv₂ Hgrd _
                        constructor
                        · apply CloseCourses.PO_safety₁ ; assumption
                        · apply CloseCourses.PO_safety₂ ; assumption
  variant := CloseCourses.variant
  convergence := fun cs m => by simp [Machine.invariant, -CloseCourses.guard]
                                intros
                                apply CloseCourses.PO_convergence
                                assumption
  }

end M0

end CoursesSpec
