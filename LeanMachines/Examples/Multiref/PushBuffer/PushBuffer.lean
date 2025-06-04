import Mathlib.Tactic

import LeanMachines.Event.Basic
import LeanMachines.Event.Ordinary
import LeanMachines.Event.Convergent
import LeanMachines.Refinement.Relational.Basic
import LeanMachines.Refinement.Relational.Ordinary



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

/-- Initialization event (no parameter, empty buffer)-/
def B0.Init : InitEvent (B0 ctx) Unit Unit :=
  newInitEvent'' {
    init _ := { size := 0 }
    safety := fun _ => by simp [Machine.invariant]
  }

/-- Event: adding an element to the buffer (no parameter,
since we only track the number of elements)-/
def B0.Put : OrdinaryEvent (B0 ctx) Unit Unit :=
  newEvent'' {
    guard := fun b0 => b0.size < ctx.maxSize
    action := fun b0 _ => { size := b0.size + 1 }
    safety := fun b0 =>
      by
        simp[Machine.invariant]
        intros hinv hgrd
        exact hgrd

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

/-First step of refinement : a stack of values -/

structure B1 (ctx : BufContext) (α : Type u) where
  /-- The current size of the buffer -/
  stack : List α




instance : Machine BufContext (B1 ctx α) where
  context := ctx
  invariant b1 := b1.stack.length ≤ ctx.maxSize


def B1.Init : InitEvent (B1 ctx α) Unit Unit :=
  newInitEvent'' {
    init _ := { stack := [] }
    safety := fun _ => by simp [Machine.invariant]
  }



/- Refinement between B0 and B1 -/
instance {ctx α} : Refinement (B0 ctx) (B1 ctx α) where
  refine am m       := am.size = m.stack.length
  refine_safe am m  :=
    by
      simp[Machine.invariant]
      intros hinv_ccr href
      rw[href]
      exact hinv_ccr

def B1.Put : OrdinaryREvent (B0 ctx) (B1 ctx α) B0.Put α Unit :=
  newREvent' B0.Put {
    guard m _ := m.stack.length < ctx.maxSize
    action m x hgrd := {stack := x::m.stack}
    safety m x hgrd :=
      by
        simp[Machine.invariant]
        intros
        assumption

    lift_in := λx => ()
    strengthening m x :=
      by
        intros Hinv Hgrd am href
        simp[B0.Put]
        rw[href]
        assumption
    simulation m x :=
      by
        simp[Refinement.refine]
        intros Hinv Hgrd am Href
        simp[B0.Put]
        assumption
  }


/- Multi-ref : new abstract machine-/
structure Button where
  pushed : Bool

instance: Machine Unit Button where
  context := ()
  invariant _ := True

def Button.Init : InitEvent Button Unit Unit :=
  newInitEvent''
  {
    init _ := {pushed := false}
    safety _ := by simp[Machine.invariant]
  }
def Button.Push : OrdinaryEvent Button Unit Unit :=
  newEvent'' {
    guard := fun st => ¬ st.pushed
    action := fun _ _ => { pushed := true }
    safety := fun st => by simp [Machine.invariant]
  }

def Button.Release : OrdinaryEvent Button Unit Unit :=
  newEvent'' {
    guard := fun st => st.pushed
    action := fun _ _ => { pushed := false }
    safety := fun st => by simp [Machine.invariant]
  }

/-!

## Step 2 : the Push Buffer

The Push Buffer state is simply the merging of two
abstract states: the abstract buffer `B1` and the `Button`.

-/

structure PushBuffer (ctx : BufContext) (α : Type u)
  extends Button where
  stack : List α

/-!
Of course the machine itself merges the invariants.
-/

instance: Machine BufContext (PushBuffer ctx α ) where
  context := ctx
  invariant := fun pb => pb.stack.length ≤ ctx.maxSize


instance: Refinement (B0 ctx) (PushBuffer ctx α) where
  refine b0 pb := b0.size = pb.stack.length
  refine_safe am m :=
    by
      simp[Machine.invariant]
      intros hinv href
      rw[href]
      exact hinv

instance: Refinement Button (PushBuffer ctx α) where
  refine btn0 pb := pb.toButton = btn0
  refine_safe :=
    by
      simp[Machine.invariant]


def PushBuffer.Init : InitEvent (PushBuffer ctx α) Unit Unit :=
  newInitEvent''
  {
    init _ := {
      stack := []
      pushed := false
    }
    safety _ := by simp[Machine.invariant]
  }


instance : SafeInitREventPO
  (PushBuffer.Init (ctx := ctx) (α := α)).to_InitEvent
  (AM := Button)
  Button.Init.to_InitEvent
  (instSafeEv := safeInitEventPO_InitEvent PushBuffer.Init)
  (instSafeAbs := safeInitEventPO_InitEvent Button.Init)
  where
  lift_in := id
  lift_out := id
  strengthening := by simp[PushBuffer.Init,Button.Init]
  simulation := by simp[Refinement.refine,PushBuffer.Init,Button.Init]

instance : SafeInitREventPO
  (PushBuffer.Init (ctx := ctx)).to_InitEvent
  (AM := B0 ctx)
  (M := PushBuffer ctx α)
  B0.Init.to_InitEvent
  (instSafeEv := safeInitEventPO_InitEvent PushBuffer.Init)
  (instSafeAbs := safeInitEventPO_InitEvent B0.Init)
  where
  lift_in := id
  lift_out := id
  strengthening := by simp[PushBuffer.Init,B0.Init]
  simulation :=
    by
      simp[Refinement.refine,PushBuffer.Init,B0.Init]


/- Event which is a double refinement -/
def PushBuffer.PushAdd : OrdinaryEvent (PushBuffer ctx α) α Unit :=
  newEvent'
  {
    guard m _    := ¬ m.pushed ∧ m.stack.length + 1 ≤ ctx.maxSize
    action m x _  := { stack := x::m.stack, pushed := true}
    safety := by simp[Machine.invariant]
  }

instance : SafeREventPO
  (PushBuffer.PushAdd (ctx := ctx)).toEvent
  (AM := Button)
  (M := PushBuffer ctx α)
  Button.Push.toEvent
  (instSafeEv := instSafeEventPO_OrdinaryEvent PushBuffer.PushAdd)
  (instSafeAbs := instSafeEventPO_OrdinaryEvent Button.Push)
  (valid_kind := by simp)
  where
    lift_in := λ _ => ()
    lift_out := id
    simulation m x hinv hgrd :=
      by
        simp[Machine.invariant,Refinement.refine]
        simp[PushBuffer.PushAdd,Button.Push]
    strengthening m x :=
      by
        simp[Machine.invariant,Refinement.refine]
        simp[PushBuffer.PushAdd,Button.Push]
        intros
        assumption


instance : SafeREventPO
  (PushBuffer.PushAdd (ctx := ctx) (α := α)).toEvent
  (AM := B0 ctx)
  B0.Put.toEvent
  (instSafeEv := instSafeEventPO_OrdinaryEvent PushBuffer.PushAdd)
  (instSafeAbs := instSafeEventPO_OrdinaryEvent B0.Put)
  (valid_kind := by simp)
  where
    lift_in := λ _ => () ; lift_out := id
    strengthening m x :=
      by
        simp[Machine.invariant,Refinement.refine]
        simp[PushBuffer.PushAdd,B0.Put]
        intros hinv hgrd₁ hgrd₂ am href
        rw[href]
        assumption
    simulation m x hinv hgrd :=
      by
        simp[Machine.invariant,Refinement.refine]
        simp[PushBuffer.PushAdd,B0.Put]


/-



-/
