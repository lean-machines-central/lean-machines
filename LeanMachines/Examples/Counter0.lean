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
  default := {cpt :=0}



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
def Counter0.Set_count : Event (Counter0 ctx) Nat Unit :=
  {
    action := fun c0 v _ => ((),{cpt:= c0.cpt + v})
    guard := fun c0 v => 0 ≤ (c0.cpt + v) ∧ (c0.cpt + v) ≤ ctx.max
  }

instance : SafeEvent (Counter0.Set_count (ctx := ctx)) where
  safety :=
    fun m v hinvm =>
      by
        simp[Machine.invariant]
        simp[Counter0.Set_count]

/-
  After showing that the event is indeed safe, we can turn it into an OrdinaryEvent with the safe constructor.
  This allows us to use the algebraic properties shown for the OrdinaryEvent structure.
-/
def Counter0.Set_count' : OrdinaryEvent (Counter0 ctx) Nat Unit := mkOrdinaryEvent (Counter0.Set_count)
