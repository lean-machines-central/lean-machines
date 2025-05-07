import Mathlib.Tactic

import LeanMachines.Event.Basic
import LeanMachines.Event.Ordinary
import LeanMachines.Examples.Multiref.Press.Weak_reaction
import LeanMachines.Refinement.Relational.Basic
import LeanMachines.Refinement.Relational.Ordinary
import LeanMachines.Examples.Multiref.Press.Strong_reaction



/-

  First step of the description of the mechanical press:

  The controller is connected to the motor via a strong
  reaction pattern. To formalize that, we're going
  to refine the pattern Strong_reaction
-/

/-
  Axioms 0_1 and 0_2 : the two variables describing
  the interaction between the controller and the motor
  have a status
-/
inductive Status where
  | stopped : Status
  | working : Status
def Status.toBool (s : Status) :=
  match s with
  | stopped => false
  | working => true
@[simp]
def Status.ofBool (s : Bool) :=
  match s with
  | true => working
  | false => stopped
open Status
/-
  The machine has two variables :
    - motor_actuator, which models the command sent by the
    controller to the motor (action),
    - motor_sensor, which models the feedback from the motor
    (reaction).
-/

structure MP0_ctx where

structure MP0  where
  -- motor : StrongReaction
  motor_actuator : Status -- a
  motor_sensor : Status   -- r
  motor_cr : Nat
  motor_ca : Nat
  start_motor_btn : Bool      -- a
  start_motor_impulse : Bool  -- r
  start_cr : Nat
  start_ca : Nat
  stop_motor_btn : Bool     -- a
  stop_motor_impulse : Bool -- r
  stop_cr : Nat
  stop_ca : Nat


instance : Machine MP0_ctx MP0 where
  context := {}
  invariant m :=
    (m.motor_cr ≤ m.motor_ca) -- pat0_5
    ∧ (m.motor_actuator = working ∧ m.motor_sensor = stopped → m.motor_cr < m.motor_ca) -- pat0_6
    ∧ (m.motor_ca ≤ m.motor_cr + 1) -- pat1_1
    ∧ ((m.motor_actuator = stopped ∨ m.motor_sensor = working) → m.motor_ca = m.motor_cr) -- pat1_4

    ∧ (m.start_cr ≤ m.start_ca)                 -- pat0_5
    ∧ (m.start_motor_btn ∧ ¬ m.start_motor_impulse → m.start_cr < m.start_ca) -- pat0_6

    ∧ (m.stop_cr ≤ m.stop_ca)                 -- pat0_5
    ∧ (m.stop_motor_btn ∧ ¬ m.stop_motor_impulse → m.stop_cr < m.stop_ca) -- pat0_6


instance : Refinement StrongReaction MP0 where
  refine am m :=
    am.ca = m.motor_ca ∧ am.cr = m.motor_cr
    -- correspondance between the type Status and the type Bool
    ∧ am.a = m.motor_actuator.toBool
    ∧ am.r = m.motor_sensor.toBool
    ∧ ofBool am.a = m.motor_actuator
    ∧ ofBool am.r = m.motor_sensor
  refine_safe am m :=
    by
      simp[Machine.invariant]
      intros pat0_5 pat0_6 pat1_1 pat1_4 _ _ _ _
      intros hr₁ hr₂ hr₃ hr₄ hr₅ hr₆
      rw[hr₁,hr₂,hr₃,hr₄]
      constructor
      · assumption
      · constructor
        · intro ha hr
          rw[ha] at hr₃
          rw[hr] at hr₄
          simp[hr₃] at hr₅
          simp[hr₄] at hr₆
          exact (pat0_6 (Eq.symm hr₅) (Eq.symm hr₆))
        · constructor
          · assumption
          · intro h
            cases h
            case inl ha =>
              rw[ha] at hr₃
              simp[hr₃] at hr₅
              exact (pat1_4 (Or.inl (Eq.symm hr₅)))
            case inr hr =>
              rw[hr] at hr₄
              simp[hr₄] at hr₆
              exact (pat1_4 (Or.inr (Eq.symm hr₆)))


instance btn1 : Refinement WeakReaction MP0 where
  refine am m :=
    am.ca = m.start_ca ∧ am.cr = m.start_cr
    ∧ am.a = m.start_motor_btn
    ∧ am.r = m.start_motor_impulse
  refine_safe am m :=
  by
    simp[Machine.invariant]
    intros _ _ _ _ pat0_5 pat0_6 _ _
    intros hr₁ hr₂ hr₃ hr₄
    rw[hr₁,hr₂,hr₃,hr₄]
    constructor
    assumption
    assumption

instance btn2 : Refinement WeakReaction MP0 where
  refine am m :=
    am.ca = m.stop_ca ∧ am.cr = m.stop_cr
    ∧ am.a = m.stop_motor_btn
    ∧ am.r = m.stop_motor_impulse
  refine_safe am m :=
  by
    simp[Machine.invariant]
    intros _ _ _ _ pat0_5 pat0_6 _ _
    intros hr₁ hr₂ hr₃ hr₄
    rw[hr₁,hr₂,hr₃,hr₄]
    constructor
    assumption
    assumption


def MP0.treat_start_button : OrdinaryEvent MP0 Unit Unit :=
  newEvent''
  {
    guard m :=
      ¬ m.start_motor_impulse
      ∧ m.start_motor_btn
      ∧ m.motor_actuator = stopped
      ∧ m.motor_sensor = working
    action m _ :=
      ⟨working,
      m.motor_sensor,
      m.motor_cr,
      m.motor_ca + 1,
      m.start_motor_btn,  -- a
      true, -- r
      m.start_cr +1,
      m.start_ca,
      m.stop_motor_btn,     -- a
      m.stop_motor_impulse, -- r
      m.stop_cr,
      m.stop_ca
      ⟩
    safety m :=
    by
      simp[Machine.invariant]
      intros m_pat0_5 m_pat0_6 m_pat1_1 m_pat1_4
      intros start_pat0_5 start_pat0_6 _ _
      intro hgrd₁ hgrd₂ hgrd₃ hgrd₄
      constructor
      · exact Nat.le_add_right_of_le m_pat0_5
      constructor
      · intro hf
        rw[hf] at hgrd₄
        contradiction
      constructor
      · exact (Nat.le_of_eq (m_pat1_4 (Or.inl hgrd₃) ))
      constructor
      · intro h
        sorry
      constructor
      · exact start_pat0_6 hgrd₂ hgrd₁
      constructor
      · assumption
      assumption
  }
