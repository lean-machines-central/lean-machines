import Mathlib.Tactic

import LeanMachines.Event.Basic
import LeanMachines.Event.Ordinary
--import LeanMachines.Event.Convergent

--import LeanMachines.NonDet.Ordinary
--import LeanMachines.NonDet.Convergent

/-!
# The Buffer example

This is a very simple example specification of a bounded buffer, developed in
three refinement steps:

 1. An abstract machine `Buffer0` (this file), only tracking the number of buffered elements

 2. A more concrete machine `Buffer1` (file `Buffer1.lean`), which actually buffers elements
  in a list, managed in a non-deterministic way

 3. A functional (deterministic) machine `Buffer2` (file `Buffer2.lean`) that uses a list representation
  and puts/retrieves elements using a priority-scheme

The proof obligations are rather trivial, except for the last step since priorities "break"
the structural induction principle of lists.

This is the running illustrative example of the IFM2024 paper:

    Stateful Functional Modeling with Refinement (a Lean4 framework)

-/

/-!

## Abstract machine

At the most abstract level, only the number of elements in the buffer is tracked.

-/

namespace Buffer

/-- The (shared) context for all the machines -/
structure BufContext where
  /-- The maximum size of the buffer -/
  maxSize : Nat
  maxSizeProp : maxSize > 0

/-- The state of the abstract machine -/
structure B0 (ctx : BufContext) where
  /-- The current size of the buffer -/
  size : Nat

/-- The instantiation of the machine -/
instance: Machine BufContext (B0 ctx) where
  context := ctx
  invariant b0 := b0.size ≤ ctx.maxSize
  default := { size := 0 }

/-- Initialization event (no parameter, empty buffer)-/
def B0.Init : OrdinaryEvent (B0 ctx) Unit Unit :=
  newInitEvent'' {
    init _ :=  { size := 0 }
    safety _ := by simp [Machine.invariant]
  }

/-- Event: adding an element to the buffer (no parameter,
since we only track the number of elements)-/
def B0.Put : OrdinaryEvent (B0 ctx) Unit Unit :=
  newEvent'' {
    guard := fun b0 => b0.size < ctx.maxSize
    action := fun b0 _ => { size := b0.size + 1 }
    safety := fun b0 => by exact fun _ Hgrd => Hgrd
  }

/-- Event : fetching (retrieving) an element.
At the abstract level, this meanins just decrementing the size.
The Event is proved convergent.
-/
def B0.Fetch : ConvergentEvent Nat (B0 ctx) Unit Unit :=
  newConvergentEvent'' {
    guard := fun b0 => b0.size > 0
    action := fun b0 _ => { size := b0.size - 1 }
    safety := fun b0 => by
      simp [Machine.invariant]
      intros H _
      exact Nat.le_add_right_of_le H

    variant := fun b0 => b0.size
    convergence := fun b0 => by
      simp [Machine.invariant]
  }

/-- Event : querying the current size of the buffer. -/
def B0.GetSize : OrdinaryEvent (B0 ctx) Unit Nat :=
  newEvent {
    action := fun b0 () _ => (b0.size, b0)
    safety := fun b0 () => by simp
  }

/-- Event : inserting an unspecified number of elements
 (non-deterministic event) -/
def B0.Batch : OrdinaryNDEvent (B0 ctx) Unit Unit :=
  newNDEvent'' {
    guard := fun b0 => b0.size < ctx.maxSize
    effect := fun b0 _ b0'  => ∃ n > 0, b0'.size = b0.size + n ∧ b0'.size ≤ ctx.maxSize

    feasibility := fun b0 => by
      simp [Machine.invariant]
      intros _ Hgrd
      exists { size := b0.size + 1 }
      exists 1

    safety := fun b0 => by simp [Machine.invariant]
  }

end Buffer
