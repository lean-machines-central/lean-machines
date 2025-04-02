import Mathlib.Tactic

import LeanMachines.Event.Basic
import LeanMachines.Event.Ordinary

/-!
  # Multi-refinement example : the tank example

  The goal of this example is to specify two abstract machines, and then use them to do a multi-refinement describing a tank


  ## Abstract machine 2, a Xor between two boolans

  For the second abstract machine, we specify the behaviour of two booleans which can never be true at the same time.

-/

/-
  The definition of an abstract machine remains the same as the previous version of the framework
-/

structure XorContext where

structure Xor0 (ctx : XorContext) where
  x : Bool
  y : Bool

instance : Machine XorContext (Xor0 ctx) where
  context := ctx
  invariant d0 := ¬ (d0.x ∧ d0.y)



def Xor0.Init : InitEvent (Xor0 ctx) Unit Unit:=
  newInitEvent''
  {
    init _ := {x := false, y := false}
    guard := True
    safety := fun _ => by simp[Machine.invariant]
  }




/- Setters for the first boolean -/

/- This event sets the first boolean with the value true -/
def Xor0.SetX_true : OrdinaryEvent (Xor0 ctx) Unit Unit :=
  newEvent''
  {
    action m _ := {x:= true, y := m.y}
    guard m := m.y = false
    safety :=
      by
        simp[Machine.invariant]
  }


/- This event sets the first boolean with the value false -/
def Xor0.SetX_false : OrdinaryEvent (Xor0 ctx) Unit Unit :=
  newEvent''
  {
    action m _ := {x:= false, y := m.y}
    guard _ := True
    safety := by simp[Machine.invariant]
  }

/- This event sets the second boolean with the value true -/

def Xor0.SetY_true : OrdinaryEvent (Xor0 ctx) Unit Unit :=
  newEvent''
  {
    action m _ := {x := m.x, y := true}
    guard m := m.x = false
    safety := by simp[Machine.invariant]
  }


/- This event sets the second boolean with the value false -/

def Xor0.SetY_false : OrdinaryEvent (Xor0 ctx) Unit Unit :=
  newEvent''
  {
    action m _ := {x := m.x, y := false}
    guard m := m.x = false
    safety := by simp[Machine.invariant]

  }
