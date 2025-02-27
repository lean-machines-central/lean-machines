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


/- In order to define an initialisation event, we firstly create it without considering the safety proof obligation -/

def Xor0.Init : InitEvent (Xor0 ctx) Unit Unit :=
  {
    init _ _ := ((),{x := false, y := false})
    guard _ := True
  }

/- Then we instanciate the SafeInitEvent typeclass, which represents the safety proof obligation -/

instance : SafeInitEvent (Xor0.Init (ctx := ctx)) where
  safety := fun x hgrd =>
    by
      simp[Machine.invariant]
      intro hf
      simp[Xor0.Init]


/- It's the same idea for regular events -/


/- Setters for the first boolean -/

/- This event sets the first boolean with the value true -/
def Xor0.SetX_true : Event (Xor0 ctx) Unit Unit :=
  {
    kind := EventKind.TransDet (Convergence.Ordinary)
    action m _ _ := ((), {x:= true, y := m.y})
    guard m _ := m.y = false
  }

instance : SafeEvent (Xor0.SetX_true (ctx:= ctx))  (EventKind.TransDet (Convergence.Ordinary)) where
  safety := by simp[Machine.invariant,Xor0.SetX_true]

/- This event sets the first boolean with the value false -/
def Xor0.SetX_false : Event (Xor0 ctx) Unit Unit :=
  {
    kind := EventKind.TransDet (Convergence.Ordinary)
    action m _ _ := ((), {x:= false, y := m.y})
    guard _ _ := True
  }
instance : SafeEvent (Xor0.SetX_false (ctx:=ctx)) (EventKind.TransDet (Convergence.Ordinary))  where
  safety := by simp[Machine.invariant,Xor0.SetX_false]

/- This event sets the second boolean with the value true -/

def Xor0.SetY_true : Event (Xor0 ctx) Unit Unit :=
  {
    kind := EventKind.TransDet (Convergence.Ordinary)
    action m _ _ := ((), {x := m.x, y := true})
    guard m _ := m.x = false
  }

instance : SafeEvent (Xor0.SetY_true (ctx:=ctx)) (EventKind.TransDet (Convergence.Ordinary)) where
  safety := by simp[Machine.invariant, Xor0.SetY_true]

/- This event sets the second boolean with the value false -/

def Xor0.SetY_false : Event (Xor0 ctx) Unit Unit :=
  {
    kind := EventKind.TransDet (Convergence.Ordinary)
    action m _ _ := ((), {x := m.x, y := false})
    guard m _ := m.x = false
  }

instance : SafeEvent (Xor0.SetY_false (ctx:=ctx)) (EventKind.TransDet (Convergence.Ordinary)) where
  safety := by simp[Machine.invariant, Xor0.SetY_false]
