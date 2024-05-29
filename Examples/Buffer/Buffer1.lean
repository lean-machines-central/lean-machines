import Mathlib.Tactic

import EventSystems.Refinement.Functional.Basic
import EventSystems.Refinement.Functional.Convergent
import EventSystems.Refinement.Relational.NonDet.Det.Convergent
-- import EventSystems.Refinement.Functional.NonDet.Det.Convergent

import Examples.Buffer.Buffer0

namespace Buffer

structure B1 (ctx : B0.Context) (α : Type) where
  data : List α

instance: Machine B0.Context (B1 ctx α) where
  context := ctx
  invariant b1 := b1.data.length ≤ ctx.maxSize
  reset := { data := [] }

@[simp]
def Buffer1.lift (b1 : B1 ctx α) : B0 ctx :=
  { size := b1.data.length }

instance: FRefinement (B0 ctx) (B1 ctx α) where
  refine := defaultRefine Buffer1.lift

  refine_safe b0 b1 := by simp [Machine.invariant] ; intros ; simp [*]

  refine_uniq b0 b0' b1 := by simp [Machine.invariant] ; intros ; simp [*]

  lift := Buffer1.lift
  lift_ref := fun b1 => by simp

def Init : InitREvent (B0 ctx) (B1 ctx α) Unit Unit :=
  newInitFREvent'' B0.Init {
    init := { data := [] }
    safety := fun _ => by simp [Machine.invariant]
    strengthening := by simp [B0.Init]
    simulation := by simp [FRefinement.lift, B0.Init]
  }

def Put : ConvergentREvent Nat (B0 ctx) (B1 ctx α) α Unit Unit Unit :=
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

def Fetch : ConvergentREvent Nat (B0 ctx) (B1 ctx α) Unit (Option α) Unit Unit :=
  newConvergentFREvent B0.Fetch.toOrdinaryEvent {
    guard := fun b1 _ => b1.data.length > 0
    action := fun b1 _ => match b1.data with
                          | x::xs => (some x, { data := xs })
                          | [] => (none, b1)
    safety := fun b1 _ => by
      simp [Machine.invariant]
      split
      case h_1 _ x xs =>
        simp [xs]
        intro Hinv
        exact Nat.le_of_succ_le Hinv
      case h_2 => intros; simp [*]
    lift_in := id
    lift_out := fun _ => ()
    strengthening := fun b1 _ => by
      simp [Machine.invariant, B0.Fetch, FRefinement.lift]
    simulation := fun b1 _ => by
      simp [Machine.invariant, B0.Fetch, FRefinement.lift]
      cases b1.data <;> simp
    variant := fun b1 => b1.data.length
    convergence := fun b1 _ => by
      simp [Machine.invariant]
      cases b1.data <;> simp
  }

def Batch : ConvergentRDetEvent Nat (B0 ctx) (B1 ctx α) (List α) Unit Unit Unit :=
  newConvergentRDetEvent' B0.Batch {
    guard := fun b1 xs => xs.length > 0 ∧ b1.data.length + xs.length ≤ ctx.maxSize
    action := fun b1 xs => { data := b1.data ++ xs }
    lift_in := fun _ => ()
    safety := fun b1 xs => by simp [Machine.invariant]
    strengthening := fun b1 xs => by
      simp [Machine.invariant, Refinement.refine, B0.Batch]
      intros Hinv Hgrd
      intro Hlen
      cases xs
      case nil => contradiction
      case cons x xs =>
        simp at Hlen
        simp_arith [Hlen]
        omega
    simulation := fun b1 xs => by
      simp [Machine.invariant, Refinement.refine, B0.Batch]
      intros _ Hgrd₁ Hgrd₂
      exists xs.length
      simp [*]
    variant := fun b1 => ctx.maxSize - b1.data.length
    convergence := fun b1 xs => by
      simp [Machine.invariant]
      intros Hinv Hgrd₁ Hgrd₂
      cases xs
      case nil => contradiction
      case cons x xs =>
        simp at *
        omega
  }

def GetSize : OrdinaryREvent (B0 ctx) (B1 ctx α) Unit Nat :=
  newREvent B0.GetSize {
    action := fun b1 _ => (b1.data.length, b1)
    lift_in := fun x => x
    lift_out := fun n => n
    safety := fun b1 _ => by simp
    strengthening := fun b1 _ => by
      simp [Machine.invariant, Refinement.refine, B0.GetSize]
    simulation := fun b1 _ => by
      simp [Machine.invariant, Refinement.refine, B0.GetSize]
  }

end Buffer
