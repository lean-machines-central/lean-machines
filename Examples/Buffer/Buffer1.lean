import Mathlib.Tactic

import EventSystems.Refinement.Functional.Basic
import EventSystems.Refinement.Functional.Convergent

import Examples.Buffer.Buffer0

namespace Buffer

structure Buffer1 (ctx : B0.Context) (α : Type) where
  data : List α

instance: Machine B0.Context (Buffer1 ctx α) where
  context := ctx
  invariant b1 := b1.data.length ≤ ctx.maxSize
  reset := { data := [] }

@[simp]
def Buffer1.lift (b1 : Buffer1 ctx α) : B0 ctx :=
  { size := b1.data.length }

instance: FRefinement (B0 ctx) (Buffer1 ctx α) where
  refine := defaultRefine Buffer1.lift

  refine_safe b0 b1 := by simp [Machine.invariant] ; intros ; simp [*]

  refine_uniq b0 b0' b1 := by simp [Machine.invariant] ; intros ; simp [*]

  lift := Buffer1.lift
  lift_ref := fun b1 => by simp

def Init : InitREvent (B0 ctx) (Buffer1 ctx α) Unit Unit :=
  newInitFREvent'' B0.Init {
    init := { data := [] }
    safety := fun _ => by simp [Machine.invariant]
    strengthening := by simp [B0.Init]
    simulation := by simp [FRefinement.lift, B0.Init]
  }

def Put : ConvergentREvent Nat (B0 ctx) (Buffer1 ctx α) α Unit Unit Unit :=
  newConvergentFREvent' B0.Put {
    guard := fun b1 _ => b1.data.length < ctx.maxSize
    action := fun b1 x => { data := x :: b1.data }

    lift_in := fun _ => ()

    safety := fun b1 x => by
      simp [Machine.invariant] ; intros ; linarith

    strengthening := fun b1 _ => by
      simp [Machine.invariant, B0.Put, FRefinement.lift]

    simulation := fun b1 _ => by
      simp [Machine.invariant, B0.Put, FRefinement.lift]

    variant := fun b1 => ctx.maxSize - b1.data.length

    convergence := fun b1 x => by
      simp [Machine.invariant] ; intros ; omega

  }

def Fetch : ConvergentREvent Nat (B0 ctx) (Buffer1 ctx α) Unit α Unit Unit :=
  newConvergentFREvent B0.Fetch.toOrdinaryEvent {
    guard := fun b1 _ => b1.data.length > 0
    action := fun b1 _ => match b1.data with
                          | x::xs => (x, { data := xs })
                          | [] => -- TODO
  }

end Buffer
