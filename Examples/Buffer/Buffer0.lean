import Mathlib.Tactic

import LeanMachines.Event.Basic
import LeanMachines.Event.Ordinary
import LeanMachines.Event.Convergent

import LeanMachines.NonDet.Ordinary
import LeanMachines.NonDet.Convergent

namespace Buffer

structure BufContext where
  maxSize : Nat
  maxSizeProp : maxSize > 0

structure B0 (ctx : BufContext) where
  size : Nat

instance: Machine BufContext (B0 ctx) where
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
    safety := fun b0 => by exact fun _ Hgrd => Hgrd
  }

def B0.Fetch : ConvergentEvent Nat (B0 ctx) Unit Unit :=
  newConvergentEvent'' {
    guard := fun b0 => b0.size > 0
    action := fun b0 => { size := b0.size - 1 }
    safety := fun b0 => by
      simp [Machine.invariant]
      intros H _
      exact Nat.le_add_right_of_le H

    variant := fun b0 => b0.size
    convergence := fun b0 => by
      simp [Machine.invariant]
  }

def B0.GetSize : OrdinaryEvent (B0 ctx) Unit Nat :=
  newEvent {
    action := fun b0 () => (b0.size, b0)
    safety := fun b0 () => by simp
  }

def B0.Batch : OrdinaryNDEvent (B0 ctx) Unit Unit :=
  newNDEvent'' {
    guard := fun b0 => b0.size < ctx.maxSize
    effect := fun b0 b0' => ∃ n > 0, b0'.size = b0.size + n ∧ b0'.size ≤ ctx.maxSize

    feasibility := fun b0 => by
      simp [Machine.invariant]
      intros _ Hgrd
      exists { size := b0.size + 1 }
      exists 1

    safety := fun b0 => by simp [Machine.invariant]
  }

end Buffer
