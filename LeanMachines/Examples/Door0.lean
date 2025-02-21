import Mathlib.Tactic

import LeanMachines.Event.Basic
import LeanMachines.Event.Ordinary

/-!
  # Multi-refinement example : the tank example

  The goal of this example is to specify two abstract machines, and then use them to do a multi-refinement describing a tank


  ## Abstract machine 2, a sluice

  For the second abstract machine, we focus on the way the tank will open/close its doors.

  Essentially, it can be represented by a boolean per door (true if opened, false if closed), and the invariant stating that
  both doors can't be simultaneously opened


-/

/-
  The definition of an abstract machine remains the same as the previous version of the framework
-/

structure DoorsContext where

structure Doors0 (ctx : DoorsContext) where
  b_in : Bool
  b_out : Bool

instance : Machine DoorsContext (Doors0 ctx) where
  context := ctx
  default := { b_in := false, b_out := false}
  invariant d0 := ¬ (d0.b_in ∧ d0.b_out)


/- In order to define an initialisation event, we firstly create it without considering the safety proof obligation -/

def Doors0.Init : InitEvent (Doors0 ctx) Unit Unit :=
  {
    init _ _ := ((),{b_in := false, b_out := false})
    guard _ := True
  }

/- Then we instanciate the SafeInitEvent typeclass, which represents the safety proof obligation -/

instance : SafeInitEvent (Doors0.Init (ctx := ctx)) where
  safety := fun x hgrd =>
    by
      simp[Machine.invariant]
      intro hf
      simp[Doors0.Init]


/- It's the same idea for regular events -/

def Doors0.Set_in : Event (Doors0 ctx) Bool Unit :=
  {
    action := fun d0 x _ => ((),{b_in := x, b_out := d0.b_out})
    guard := fun d0 x => ¬ (x ∧ d0.b_out)
  }

instance : SafeEvent (Doors0.Set_in (ctx := ctx)) where
  safety := fun m x =>
    by
      simp[Machine.invariant]
      simp[Doors0.Set_in]


def Doors0.Set_out : Event (Doors0 ctx) Bool Unit :=
  {
    action := fun d0 x _ => ((),{b_out := x, b_in := d0.b_in})
    guard := fun d0 x => ¬ (d0.b_in ∧ x)
  }

instance : SafeEvent (Doors0.Set_out (ctx := ctx)) where
  safety := fun m x  =>
    by
      simp[Machine.invariant, Doors0.Set_out]
