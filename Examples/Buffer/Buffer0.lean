import Mathlib.Tactic

import EventSystems.Event.Basic
import EventSystems.Event.Ordinary
import EventSystems.Event.Convergent

namespace Buffer

structure B0.Context where
  maxSize : Nat
  maxSizeProp : maxSize > 0

structure B0 (ctx : B0.Context) where
  size : Nat

instance: Machine B0.Context (B0 ctx) where
  context := ctx
  invariant b0 := b0.size ≤ ctx.maxSize
  reset := { size := 0 }

def B0.Init : InitEvent (B0 ctx) Unit Unit :=
  newInitEvent'' {
    init := { size := 0 }
    safety := fun _ => by simp [Machine.invariant]
  }

def B0.Put : OrdinaryEvent (B0 ctx) Unit Unit :=
  newEvent'' {
    guard := fun b0 => b0.size < ctx.maxSize
    action := fun b0 => { size := b0.size + 1 }
    safety := fun b0 => by
      simp [Machine.invariant]
      intros _ Hgrd
      exact Hgrd
  }

def B0.Fetch : ConvergentEvent Nat (B0 ctx) Unit Unit :=
  newConvergentEvent'' {
    guard := fun b0 => b0.size > 0
    action := fun b0 => { size := b0.size - 1}
    safety := fun b0 => by
      simp [Machine.invariant]
      intros Hinv _
      linarith
    variant := fun b0 => b0.size
    convergence := fun b0 => by
      simp [Machine.invariant]
      intros _ Hgrd
      omega
  }

def B0.getSize : OrdinaryEvent (B0 ctx) Unit Nat :=
  newEvent {
    action := fun b0 () => (b0.size, b0)
    safety := fun b0 () => by simp
  }

end Buffer
