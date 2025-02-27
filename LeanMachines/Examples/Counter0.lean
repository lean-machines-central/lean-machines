import Mathlib.Tactic

import LeanMachines.Event.Basic
import LeanMachines.Event.Ordinary



/-!

  # Multi-refinement example : the tank example

  The goal of this example is to specify two abstract machines, and then use them to do a multi-refinement describing a tank


  ## Abstract machine 1, a simple counter

  The first abstract machine we want to consider for the tank example is a simple counter (which will ultimately represent the tank's capacity),
  with a maximum capacity

-/

/-
  The definition of an abstract machine remains the same as the previous version of the framework
-/

structure CountContext where
  max : Nat
  maxProp : max > 0


structure Counter0 (ctx : CountContext) where
  cpt : Nat


instance : Machine CountContext (Counter0 ctx) where
  context := ctx
  invariant c0 := c0.cpt ≤ ctx.max



/- In order to define an initialisation event, we firstly create it without considering the safety proof obligation -/


def Counter0.Init : InitEvent (Counter0 ctx) Unit Unit :=
  {
    init _ _ :=  ((),{cpt :=0})
    guard _ := True
  }

/- Then we instanciate the SafeInitEvent typeclass, which represents the safety proof obligation -/

instance : SafeInitEvent (Counter0.Init (ctx := ctx)) where
  safety := fun x hgrd =>
    by
      simp[Machine.invariant]
      simp[Counter0.Init]


/- It's the same idea for regular events -/

/- Our counter has two kinds of evens -/

/- Either we increment it by a Nat value -/
def Counter0.Incr : Event (Counter0 ctx) Nat Unit :=
  {
    kind := EventKind.TransDet (Convergence.Ordinary)
    action := fun c0 v _ => ((),{cpt:= c0.cpt + v})
    guard := fun c0 v => (c0.cpt + v) ≤ ctx.max
  }

instance : SafeEvent (Counter0.Incr (ctx := ctx))  (EventKind.TransDet (Convergence.Ordinary)) where
  safety := fun m v hinvm => by simp[Machine.invariant,Counter0.Incr]

/- Or we drecrement it by a Nat value -/
def Counter0.Decr : Event (Counter0 ctx) Nat Unit :=
  {
    kind := EventKind.TransDet (Convergence.Ordinary)
    action := fun c0 v _ => ((),{cpt:= c0.cpt - v})
    guard := fun _ _ => True -- No guard is necessary : we reason with Nat, if x < y then x - y = 0
  }

instance : SafeEvent (Counter0.Decr (ctx := ctx)) (EventKind.TransDet (Convergence.Ordinary)) where
  safety :=
    by
      simp[Machine.invariant,Counter0.Decr]
      omega
