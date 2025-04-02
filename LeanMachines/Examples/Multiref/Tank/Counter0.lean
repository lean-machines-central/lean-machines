import Mathlib.Tactic

import LeanMachines.Event.Basic
import LeanMachines.Event.Ordinary
import LeanMachines.Event.Convergent



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


def Counter0.Init: InitEvent (Counter0 ctx) Unit Unit :=
  newInitEvent''
  {
    init _ := {cpt :=0}
    guard := True
    safety := by simp[Machine.invariant]
  }



/- It's the same idea for regular events -/


/- Either we increment it by a Nat value -/
def Counter0.Incr : AnticipatedEvent Nat (Counter0 ctx) Nat Unit :=
  newAnticipatedEvent'
  {
    action := fun c0 v _ => {cpt:= c0.cpt + v}
    guard := fun c0 v => (c0.cpt + v) ≤ ctx.max
    safety := fun m v hinvm => by simp[Machine.invariant]
    variant := fun m => ctx.max - m.cpt
    nonIncreasing := fun m x hinv hgrd =>
      by
        simp
        omega
  }

/- Or we drecrement it by a Nat value -/
def Counter0.Decr : ConvergentEvent Nat (Counter0 ctx) Nat Unit :=
  newConvergentEvent'
  {
    action := fun c0 v _ => {cpt:= c0.cpt - v}
    guard := fun m v => m.cpt ≥ v ∧ v > 0
    safety :=
    by
      simp[Machine.invariant]
      omega
    variant := fun m => m.cpt
    convergence :=
    by
      simp[Machine.invariant,Variant.variant]
      intros m x hinv hgrd₁ hgrd₂
      omega
  }



def Counter0.setCount : OrdinaryEvent (Counter0 ctx) Nat Unit :=
  newEvent'
  {
    action := fun _ v _ => {cpt:=v}
    guard := fun _ v => (v ≤ ctx.max)
    safety :=
      fun m x =>
        by
          simp[Machine.invariant]
  }
