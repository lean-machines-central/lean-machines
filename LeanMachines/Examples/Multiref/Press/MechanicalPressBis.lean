import Mathlib.Tactic

import LeanMachines.Event.Basic
import LeanMachines.Event.Ordinary
import LeanMachines.Examples.Multiref.Press.Weak_reaction
import LeanMachines.Refinement.Relational.Basic
import LeanMachines.Refinement.Relational.Ordinary
import LeanMachines.Examples.Multiref.Press.Strong_reaction



/-

  We can compose machines, but there is a lot of boiler plate...
  Maybe we could find a way to compose them (with optics ?)
  automatically (using a function converting several events to
  one big composite event ?)
-/

structure MP0_ctx where

structure MP0 (ctx : MP0_ctx) where               -- We can compose abstract machines at the concrete level
  motor_controller : StrongReaction
  btn1 : WeakReaction
  btn2 : WeakReaction


instance : Machine MP0_ctx (MP0 ctx) where
  context := {}
  invariant m :=
    Machine.invariant (m.motor_controller)
    ∧ Machine.invariant (m.btn1)
    ∧ Machine.invariant (m.btn2)


def skip_strong := mkOrdinaryEvent (skip_Event StrongReaction Unit)
def skip_weak := mkOrdinaryEvent (skip_Event WeakReaction Unit)



def MP0.composeEvent
  (ev_ctrl : OrdinaryEvent StrongReaction α₁ β₁)                -- [SafeEventPO ev_ctrl k₁]
  (ev_btn1 : OrdinaryEvent WeakReaction α₂ β₂)                  -- [SafeEventPO ev_btn1 k₂]
  (ev_btn2 : OrdinaryEvent WeakReaction α₃ β₃)                  -- [SafeEventPO ev_btn2 k₃]
  : OrdinaryEvent (MP0 ctx) (α₁ × α₂ × α₃) (β₁×β₂×β₃) :=
  newEvent
  {
    guard  m  x     := ev_ctrl.guard m.motor_controller x.1
                      ∧ ev_btn1.guard m.btn1 x.2.1
                      ∧ ev_btn2.guard m.btn2 x.2.2
    action m x hgrd :=
      let (b₁,nctrl) := ev_ctrl.action m.motor_controller x.1 hgrd.1
      let (b₂,nbtn1) := ev_btn1.action m.btn1 x.2.1 hgrd.2.1
      let (b₃,nbtn2) := ev_btn2.action m.btn2 x.2.2 hgrd.2.2
      ((b₁,b₂,b₃), ⟨nctrl,nbtn1,nbtn2⟩)
    safety m x      :=
      by
        simp[Machine.invariant]
        intros hinv_m₁ hinv_m₂ hinv_m₃ hinv_m₄ hinv_btn1₁ hinv_btn1₂ hinv_btn2₁ hinv_btn2₂ hgrd
        constructor
        · have h' := ev_ctrl.safety m.motor_controller x.1
          simp[Machine.invariant] at h'
          have h'' := h' hinv_m₁ hinv_m₂ hinv_m₃ hinv_m₄
          exact h'' hgrd.1
        constructor
        · have h' := ev_btn1.safety m.btn1 x.2.1
          simp[Machine.invariant] at h'
          have h'' := h' hinv_btn1₁ hinv_btn1₂
          exact h'' hgrd.2.1
        · have h' := ev_btn2.safety m.btn2 x.2.2
          simp[Machine.invariant] at h'
          have h'' := h' hinv_btn2₁ hinv_btn2₂
          exact h'' hgrd.2.2
  }

instance [Machine CTX M]: Coe (OrdinaryEvent M α (Unit × Unit × Unit)) (OrdinaryEvent M α Unit) where
  coe ev := { guard := ev.guard
              action m x grd :=
              let (_,m') := ev.action m x grd
              ((), m')
              safety := ev.safety }

instance [Machine CTX M]: Coe (OrdinaryEvent M (Unit × Unit × Unit) β) (OrdinaryEvent M Unit β) where
  coe ev := { guard m _ := ev.guard m ((),(),())
              action m _ grd :=
              ev.action m ((),(),()) grd
              safety m _ :=
              ev.safety m ((),(),())}


def MP0.push_start_motor_button_c : OrdinaryEvent (MP0 ctx) Unit Unit :=
  MP0.composeEvent
  skip_strong
  WeakReaction.Action_on
  skip_weak
  (ctx := ctx)


def MP0.push_start_motor_button : OrdinaryEvent  (MP0 ctx) Unit Unit :=
  newEvent''
  {
    guard m       := ¬m.btn1.a
    action m hgrd := ⟨m.motor_controller, ⟨true,m.btn1.r,m.btn1.ca+1,m.btn1.cr⟩,m.btn2⟩
    safety m      :=
      by
        simp[Machine.invariant]
        intros hinv_m₁ hinv_m₂ hinv_m₃ hinv_m₄ hinv_btn1₁ hinv_btn1₂ _ _ hgrd
        constructor
        -- controller invariants
        constructor
        assumption
        constructor
        assumption
        constructor
        assumption
        assumption
        -- first btn invariants
        constructor -- We can reuse the proof ! (just need some boiler plate...)
        · have h' := WeakReaction.Action_on.safety m.btn1 ()
          simp[Machine.invariant] at h'
          have h'' := h' hinv_btn1₁ hinv_btn1₂
          simp[WeakReaction.Action_on] at h''
          exact h'' hgrd
        -- second btn invariants
        constructor
        assumption
        assumption
  }

example : ∀ ctx : MP0_ctx, MP0.push_start_motor_button (ctx := ctx) = MP0.push_start_motor_button_c :=
  by
    intro ctx
    apply OrdinaryEvent.ext
    apply Event.ext'
    intros m _
    constructor
    · simp[MP0.push_start_motor_button,MP0.push_start_motor_button_c]
      simp[WeakReaction.Action_on]
      simp[MP0.composeEvent]
      simp[skip_strong,skip_weak,mkOrdinaryEvent]
    · simp[MP0.push_start_motor_button,MP0.push_start_motor_button_c]
      simp[MP0.composeEvent]
      simp[skip_strong,skip_weak,mkOrdinaryEvent]
      simp[WeakReaction.Action_on]


def MP0.push_stop_motor_button : OrdinaryEvent (MP0 ctx) Unit Unit :=
  newEvent''
  {
    guard m       := WeakReaction.Action_on.guard m.btn2 ()
    action m hgrd :=
    ⟨
      m.motor_controller,
      m.btn1,
      (WeakReaction.Action_on.action m.btn2 () hgrd).2
    ⟩
    safety m      :=
    by
      simp[Machine.invariant]
      intros _ _ _ _ _ _ hinv_btn2₁ hinv_btn2₂ hgrd
      constructor
      · constructor
        assumption
        constructor
        assumption
        constructor
        assumption
        assumption
      constructor
      · constructor
        assumption
        assumption
      have h' := WeakReaction.Action_on.safety m.btn2 ()
      simp[Machine.invariant] at h'
      have h'' := h' hinv_btn2₁ hinv_btn2₂
      exact h'' hgrd
  }

def MP0.release_start_motor_button : OrdinaryEvent (MP0 ctx) Unit Unit :=
  newEvent''
  {
    guard m       := WeakReaction.Action_off.guard m.btn1 ()
    action m hgrd :=
    ⟨
      m.motor_controller,
      (WeakReaction.Action_off.action m.btn1 () hgrd).2,
      m.btn2
    ⟩
    safety m      :=
    by
      simp[Machine.invariant]
      intros _ _ _ _ hinv_btn1₁ hinv_btn1₂ _ _ hgrd
      constructor
      · constructor
        assumption
        constructor
        assumption
        constructor
        assumption
        assumption
      constructor
      · have h' := WeakReaction.Action_off.safety m.btn1 ()
        simp[Machine.invariant] at h'
        have h'' := h' hinv_btn1₁ hinv_btn1₂
        exact h'' hgrd
      constructor
      assumption
      assumption
  }



def MP0.release_stop_motor_button : OrdinaryEvent (MP0 ctx) Unit Unit :=
  newEvent''
  {
    guard m       := WeakReaction.Action_off.guard m.btn2 ()
    action m hgrd :=
    ⟨
      m.motor_controller,
      m.btn1,
      (WeakReaction.Action_off.action m.btn2 () hgrd).2
    ⟩
    safety m      :=
    by
      simp[Machine.invariant]
      intros _ _ _ _ _ _ hinv_btn2₁ hinv_btn2₂ hgrd
      constructor
      · constructor
        assumption
        constructor
        assumption
        constructor
        assumption
        assumption
      constructor
      · constructor
        assumption
        assumption
      · have h' := WeakReaction.Action_off.safety m.btn2 ()
        simp[Machine.invariant] at h'
        have h'' := h' hinv_btn2₁ hinv_btn2₂
        exact h'' hgrd
  }






#check (instSafeEventPO_OrdinaryEvent MP0.push_start_motor_button)

def MP0.treat_push_start_motor_button : OrdinaryEvent (MP0 ctx) Unit Unit :=
  newEvent''
  {
    guard m       :=
      (WeakReaction.Reaction_on).guard m.btn1 () ∧
      (StrongReaction.Action_on).guard m.motor_controller ()
    action m hgrd :=
      ⟨((StrongReaction.Action_on).action m.motor_controller () hgrd.2).2
      ,((WeakReaction.Reaction_on).action m.btn1 () hgrd.1).2
      ,m.btn2⟩
    safety m      :=
      by
        simp[Machine.invariant]
        intros hinv_m₁ hinv_m₂ hinv_m₃ hinv_m₄ hinv_btn1₁ hinv_btn1₂ _ _ hgrd
        constructor
        · have h' := StrongReaction.Action_on.safety m.motor_controller ()
          simp[Machine.invariant] at h'
          have h'' := h' hinv_m₁ hinv_m₂ hinv_m₃ hinv_m₄
          exact h'' hgrd.2
        constructor
        · have h' := WeakReaction.Reaction_on.safety m.btn1 ()
          simp[Machine.invariant] at h'
          have h'' := h' hinv_btn1₁ hinv_btn1₂
          exact h'' hgrd.1
        · constructor
          assumption
          assumption
  }

def MP0.treat_push_stop_motor_button : OrdinaryEvent (MP0 ctx) Unit Unit :=
  newEvent''
  {
    guard m       :=
      (WeakReaction.Reaction_on).guard m.btn2 () ∧
      (StrongReaction.Action_off).guard m.motor_controller ()
    action m hgrd :=
      ⟨((StrongReaction.Action_off).action m.motor_controller () hgrd.2).2
      , m.btn1
      ,((WeakReaction.Reaction_on).action m.btn2 () hgrd.1).2
      ⟩
    safety m      :=
      by
        simp[Machine.invariant]
        intros hinv_m₁ hinv_m₂ hinv_m₃ hinv_m₄ _ _ hinv_btn2₁ hinv_btn2₂ hgrd
        constructor
        · have h' := StrongReaction.Action_off.safety m.motor_controller ()
          simp[Machine.invariant] at h'
          have h'' := h' hinv_m₁ hinv_m₂ hinv_m₃ hinv_m₄
          exact h'' hgrd.2
        constructor
        · constructor
          assumption
          assumption
        · have h' := WeakReaction.Reaction_on.safety m.btn2 ()
          simp[Machine.invariant] at h'
          have h'' := h' hinv_btn2₁ hinv_btn2₂
          exact h'' hgrd.1
  }


def MP0.treat_release_start_motor_button : OrdinaryEvent (MP0 ctx) Unit Unit :=
  newEvent''
  {
    guard m       := WeakReaction.Reaction_off.guard m.btn1 ()
    action m hgrd :=
      ⟨
        m.motor_controller
        , (WeakReaction.Reaction_off.action m.btn1 () hgrd).2
        , m.btn2
      ⟩
    safety m      :=
    by
      simp[Machine.invariant]
      intros _ _ _ _ hinv_btn1₁ hinv_btn1₂ _ _ hgrd
      constructor
      · constructor
        assumption
        constructor
        assumption
        constructor
        assumption
        assumption
      constructor
      · have h' := WeakReaction.Reaction_off.safety m.btn1 ()
        simp[Machine.invariant] at h'
        have h'' := h' hinv_btn1₁ hinv_btn1₂
        exact h'' hgrd
      · constructor
        assumption
        assumption
  }


def MP0.treat_release_stop_motor_button : OrdinaryEvent (MP0 ctx) Unit Unit :=
  newEvent''
  {
    guard m       := WeakReaction.Reaction_off.guard m.btn2 ()
    action m hgrd :=
      ⟨
        m.motor_controller
        , m.btn1
        , (WeakReaction.Reaction_off.action m.btn2 () hgrd).2
      ⟩
    safety m      :=
    by
      simp[Machine.invariant]
      intros _ _ _ _ _ _ hinv_btn2₁ hinv_btn2₂ hgrd
      constructor
      · constructor
        assumption
        constructor
        assumption
        constructor
        assumption
        assumption
      constructor
      · constructor
        assumption
        assumption
      · have h' := WeakReaction.Reaction_off.safety m.btn2 ()
        simp[Machine.invariant] at h'
        have h'' := h' hinv_btn2₁ hinv_btn2₂
        exact h'' hgrd
  }



def MP0.motor_start : OrdinaryEvent (MP0 ctx) Unit Unit :=
  newEvent''
  {
    guard m       := StrongReaction.Reaction_on.guard m.motor_controller ()
    action m hgrd := ⟨
      (StrongReaction.Reaction_on.action m.motor_controller () hgrd).2
      , m.btn1
      , m.btn2
    ⟩
    safety m      :=
    by
      simp[Machine.invariant]
      intros hinv_m₁ hinv_m₂ hinv_m₃ hinv_m₄ _ _ _ _ hgrd
      constructor
      · have h' := StrongReaction.Reaction_on.safety m.motor_controller ()
        simp[Machine.invariant] at h'
        have h'' := h' hinv_m₁ hinv_m₂ hinv_m₃ hinv_m₄
        exact h'' hgrd
      constructor
      constructor
      assumption
      assumption
      constructor
      assumption
      assumption
  }


def MP0.motor_stop : OrdinaryEvent (MP0 ctx) Unit Unit :=
  newEvent''
  {
    guard m       := StrongReaction.Reaction_off.guard m.motor_controller ()
    action m hgrd := ⟨
      (StrongReaction.Reaction_off.action m.motor_controller () hgrd).2
      , m.btn1
      , m.btn2
    ⟩
    safety m      :=
    by
      simp[Machine.invariant]
      intros hinv_m₁ hinv_m₂ hinv_m₃ hinv_m₄ _ _ _ _ hgrd
      constructor
      · have h' := StrongReaction.Reaction_off.safety m.motor_controller ()
        simp[Machine.invariant] at h'
        have h'' := h' hinv_m₁ hinv_m₂ hinv_m₃ hinv_m₄
        exact h'' hgrd
      constructor
      constructor
      assumption
      assumption
      constructor
      assumption
      assumption
  }


-- False events (we need to add an event to the pattern Strong Reaction, which does nothing, in order
-- to compose events)

def StrongReaction.falseEv : OrdinaryEvent (StrongReaction) Unit Unit :=
  newEvent''
  {
    guard m   := m.a ∨ m.r
    action m _ := m
    safety m :=
    by
      intros
      assumption
  }

def MP0.treat_push_start_motor_button_false : OrdinaryEvent (MP0 ctx) Unit Unit :=
  newEvent''
  {
    guard m         := WeakReaction.Reaction_on.guard m.btn1 ()
      ∧ (m.motor_controller.a ∨ m.motor_controller.r)
    action m hgrd   := ⟨
      m.motor_controller
      , (WeakReaction.Reaction_on.action m.btn1 () hgrd.1).2
      , m.btn2
    ⟩
    safety m        :=
    by
      simp[Machine.invariant]
      intros _ _ _ _ hinv_btn1₁ hinv_btn1₂ _ _ hgrd
      constructor
      · constructor
        assumption
        constructor
        assumption
        constructor
        assumption
        assumption
      constructor
      · have h' := WeakReaction.Reaction_on.safety m.btn1 ()
        simp[Machine.invariant] at h'
        have h'' := h' hinv_btn1₁ hinv_btn1₂
        exact h'' hgrd.1
      · constructor
        assumption
        assumption
  }

def MP0.treat_push_start_motor_button_false' : OrdinaryEvent (MP0 ctx) Unit Unit :=
  MP0.composeEvent
  StrongReaction.falseEv
  WeakReaction.Reaction_on
  skip_weak
  (ctx := ctx)


example : ∀ ctx : MP0_ctx,
  MP0.treat_push_start_motor_button_false (ctx := ctx) = MP0.treat_push_start_motor_button_false' :=
  by
    intro ctx
    apply OrdinaryEvent.ext'
    intros m x
    constructor
    · simp[MP0.treat_push_start_motor_button_false,MP0.treat_push_start_motor_button_false']
      simp[MP0.composeEvent]
      simp[skip_weak,mkOrdinaryEvent]
      simp[WeakReaction.Reaction_on,StrongReaction.falseEv]
      exact Iff.symm And.comm
    · simp[MP0.treat_push_start_motor_button_false,MP0.treat_push_start_motor_button_false']
      simp[MP0.composeEvent]
      simp[skip_weak,mkOrdinaryEvent]
      simp[WeakReaction.Reaction_on,StrongReaction.falseEv]


def MP0.treat_push_stop_motor_button_false : OrdinaryEvent (MP0 ctx) Unit Unit :=
  MP0.composeEvent
  StrongReaction.falseEv
  skip_weak
  WeakReaction.Reaction_on
  (ctx := ctx)
