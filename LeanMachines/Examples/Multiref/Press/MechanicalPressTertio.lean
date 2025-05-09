import Mathlib.Tactic

import LeanMachines.Event.Basic
import LeanMachines.Event.Ordinary
import LeanMachines.Composition.Ordinary
import LeanMachines.Examples.Multiref.Press.Weak_reaction

import LeanMachines.Examples.Multiref.Press.Strong_reaction


def  MP0_ctx :=  WrCtxt × WrCtxt × WrCtxt

def MP0 (ctx : MP0_ctx) := (StrongReaction ctx.1) × (WeakReaction ctx.2.1) × (WeakReaction ctx.2.2)


def skip_strong (ctx : WrCtxt) := mkOrdinaryEvent (skip_Event (StrongReaction ctx) Unit)
def skip_weak (ctx : WrCtxt) := mkOrdinaryEvent (skip_Event (WeakReaction ctx) Unit)


/-
def MP0.push_start_motor_button_c : OrdinaryEvent (MP0 ctx) Unit Unit :=
  MP0.composeEvent
  skip_strong
  WeakReaction.Action_on
  skip_weak
  (ctx := ctx)
-/

def MP0.push_start_motor_button
  : OrdinaryEvent ((StrongReaction {}) × (WeakReaction  {}) × (WeakReaction {}))
  (Unit × Unit × Unit) (Unit × Unit × Unit)
  :=
  skip_strong {} © (WeakReaction.Action_on ) © skip_weak {}


/-
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
-/
def MP0.push_stop_motor_button :
  OrdinaryEvent ((StrongReaction {}) × (WeakReaction  {}) × (WeakReaction {}))
  (Unit × Unit × Unit) (Unit × Unit × Unit)
  :=
    skip_strong {} © skip_weak {} © (WeakReaction.Action_on )


/-
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
-/
def MP0.release_start_motor_button :
  OrdinaryEvent (MP0 ctx)
  (instM := prod )
  (Unit × Unit × Unit) (Unit × Unit × Unit)
  := skip_strong ctx.1 © WeakReaction.Action_off  © skip_weak ctx.2.2

/-
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
-/
def MP0.release_stop_motor_button :
  OrdinaryEvent (MP0 ctx)
  (instM := prod )
  (Unit × Unit × Unit) (Unit × Unit × Unit)
  :=
  skip_strong ctx.1 © skip_weak ctx.2.1 © WeakReaction.Action_off


/-
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
-/
def MP0.treat_push_start_motor_button :
  OrdinaryEvent (MP0 ctx)
  (instM := prod )
  (Unit × Unit × Unit) (Unit × Unit × Unit)
  :=
  StrongReaction.Action_on.toOrdinaryEvent © WeakReaction.Reaction_on © skip_weak ctx.2.2

/-
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
-/
def MP0.treat_push_stop_motor_button :
  OrdinaryEvent (MP0 ctx)
  (instM := prod )
  (Unit × Unit × Unit) (Unit × Unit × Unit)
  :=
  StrongReaction.Action_off.toOrdinaryEvent © skip_weak ctx.2.1 © WeakReaction.Reaction_on


/-
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
-/
def MP0.treat_release_start_motor_button :
 OrdinaryEvent (MP0 ctx)
  (instM := prod )
  (Unit × Unit × Unit) (Unit × Unit × Unit)
  :=
  skip_strong ctx.1 © WeakReaction.Reaction_on © skip_weak ctx.2.2


/-
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
-/

def MP0.treat_release_stop_motor_button :
  OrdinaryEvent (MP0 ctx)
  (instM := prod )
  (Unit × Unit × Unit) (Unit × Unit × Unit)
  :=
  skip_strong ctx.1 © skip_weak ctx.2.1 © WeakReaction.Reaction_off

/-
def MP0.motor_start : OrdinaryEvent (MP0 ctx) Unit Unit :=
  newEvent''
  {
    guard m       := StrongReaction.Reaction_on.guard m.motor_controller ()
    action m hgrd := ⟨
      (StrongReaction.Reaction_on.action m.motor_controller () hgrd).2
      , m.btn1
      , m.btn2
    ⟩
-/
def MP0.motor_start :
  OrdinaryEvent (MP0 ctx)
  (instM := prod )
  (Unit × Unit × Unit) (Unit × Unit × Unit)
  :=
  StrongReaction.Reaction_on.toOrdinaryEvent © skip_weak ctx.2.1 © skip_weak ctx.2.2

/-
def MP0.motor_stop : OrdinaryEvent (MP0 ctx) Unit Unit :=
  newEvent''
  {
    guard m       := StrongReaction.Reaction_off.guard m.motor_controller ()
    action m hgrd := ⟨
      (StrongReaction.Reaction_off.action m.motor_controller () hgrd).2
      , m.btn1
      , m.btn2
    ⟩
-/

def MP0.motor_stop :
  OrdinaryEvent (MP0 ctx)
  (instM := prod)
  (Unit × Unit × Unit) (Unit × Unit × Unit)
  :=
  StrongReaction.Reaction_off.toOrdinaryEvent © skip_weak ctx.2.1 © skip_weak ctx.2.2

/-
      False events
      These events didn't exist in the pattern, so we won't use the composition operator,
      which is totally possible even with this way of defining a machine by a product of other
      machines !
-/


def MP0.treat_push_start_motor_button_false : OrdinaryEvent (MP0 ctx) (instM := prod) Unit Unit :=
  newEvent'' (instM := prod)
  {
    guard m         := WeakReaction.Reaction_on.guard m.2.1 ()
      ∧ (m.1.a ∨ m.1.r)
    action m hgrd   := ⟨
      ((skip_strong ctx.1).action m.1 () (by simp[skip_strong,mkOrdinaryEvent])).2
      , (WeakReaction.Reaction_on.action m.2.1 () hgrd.1).2
      , ((skip_weak ctx.1).action m.2.2 () (by simp[skip_weak,mkOrdinaryEvent])).2
    ⟩
    safety m :=
    by
      simp[skip_strong,mkOrdinaryEvent,skip_weak]
      unfold Machine.invariant
      unfold prod
      simp
      intros hinv₁ hinv₂ hinv₃ hgrd
      constructor
      · assumption
      constructor
      · exact WeakReaction.Reaction_on.safety m.2.1 () hinv₂ hgrd.1
      · assumption
  }

/-
def MP0.treat_push_stop_motor_button_false : OrdinaryEvent (MP0 ctx) Unit Unit :=
  MP0.composeEvent
  StrongReaction.falseEv --     guard m   := m.a ∨ m.r action m := m
  skip_weak
  WeakReaction.Reaction_on
  (ctx := ctx)
-/


def MP0.treat_push_stop_motor_button_false : OrdinaryEvent (MP0 ctx) (instM := prod) Unit Unit :=
  newEvent'' (instM := prod)
  {
    guard m         := WeakReaction.Reaction_on.guard m.2.2 ()
      ∧ (m.1.a ∨ m.1.r)
    action m hgrd   := ⟨
      ((skip_strong ctx.1).action m.1 () (by simp[skip_strong,mkOrdinaryEvent])).2
      , ((skip_weak ctx.1).action m.2.1 () (by simp[skip_weak,mkOrdinaryEvent])).2
      , (WeakReaction.Reaction_on.action m.2.2 () hgrd.1).2

    ⟩
    safety m :=
    by
      simp[skip_strong,mkOrdinaryEvent,skip_weak]
      unfold Machine.invariant
      unfold prod
      simp
      intros hinv₁ hinv₂ hinv₃ hgrd
      constructor
      · assumption
      constructor
      · assumption
      · exact WeakReaction.Reaction_on.safety m.2.2 () hinv₃ hgrd.1
  }
