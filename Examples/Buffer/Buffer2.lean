

import Mathlib.Tactic

import EventSystems.Refinement.Strong.Basic
import EventSystems.Refinement.Strong.Convergent
import EventSystems.Refinement.Strong.Abstract
import EventSystems.Refinement.Strong.Concrete

import EventSystems.Refinement.Strong.NonDet.Det.Convergent

import Examples.Buffer.Buffer1

namespace Buffer

inductive Priority where
  | Low | Mid | Hi

structure B2 (ctx : B0.Context) (α : Type) where
  data : List (Priority × α)

instance: Machine B0.Context (B2 ctx α) where
  context := ctx
  invariant b2 := b2.data.length ≤ ctx.maxSize
  reset := { data := [] }

@[simp]
def B2.lift (b2 : B2 ctx α) : B1 ctx α :=
  { data := List.map Prod.snd b2.data }


def fetchProp [DecidableEq α] (y : α) (xs : List (Priority × α)) : Option Priority :=
  match xs with
  | [] => none
  | (p,x)::xs => if x = y then some p
                 else fetchProp y xs

def injectLow [DecidableEq α] (xs : List (Priority × α)) (ys : List α) :=
  match ys with
  | [] => []
  | y::ys => match fetchProp y xs with
             | none => (Priority.Low, y) :: injectLow xs ys
             | some p => (p, y) :: injectLow xs ys

theorem injectLow_map_prop [DecidableEq α] (xs : List (Priority × α)) (ys : List α):
  List.map Prod.snd (injectLow xs ys) = ys :=
by
  induction ys
  case nil =>
    simp [injectLow]
  case cons y ys Hind =>
    simp [injectLow]
    split <;> simp [Hind]

theorem injectLow_length_prop [DecidableEq α] (xs : List (Priority × α)) (ys : List α):
  (injectLow xs ys).length = ys.length :=
by
  induction ys
  case nil =>
    simp [injectLow]
  case cons y ys Hind =>
    simp [injectLow]
    split <;> simp [Hind]

@[simp]
def B2.unlift [DecidableEq α] (b2 : B2 ctx α) (b1' : B1 ctx α) : B2 ctx α :=
  { data := injectLow b2.data b1'.data }


instance [DecidableEq α]: SRefinement (B1 ctx α) (B2 ctx α) where
  refine := defaultRefine B2.lift
  refine_safe b1 b2 := by
    simp [Machine.invariant]
    intros Hinv Href
    rw [Href]
    simp [Hinv]

  lift := B2.lift
  lift_ref b2 := by simp [Machine.invariant]
  refine_uniq b1 b1' b2 := by
    simp [Machine.invariant, Refinement.refine]
    intros _ Href Href'
    rw [←Href'] at Href
    assumption

  unlift := B2.unlift
  lift_unlift b2 b1' := by
    simp [Machine.invariant, injectLow_map_prop]
  lu_reset b1' := by
    simp [Machine.invariant, injectLow_map_prop]


def B2.Init [DecidableEq α] : InitREvent (B1 ctx α) (B2 ctx α)  Unit Unit :=
  newAbstractInitSREvent'' B1.Init.toInitEvent {
    step_inv := by
      simp [B1.Init, Machine.invariant, SRefinement.unlift, injectLow]
  }

def B2.Put [DecidableEq α] : ConvergentREvent Nat (B1 ctx α) (B2 ctx α) α Unit :=
  newAbstractConvergentSREvent' B1.Put.toConvergentEvent {
    step_inv := fun b2 x => by
      simp [B1.Put, Machine.invariant, FRefinement.lift, SRefinement.unlift]
      intros _ Hinv'
      simp [injectLow_length_prop]
      linarith
  }

def B2.PutPrio [DecidableEq α] : ConvergentREvent Nat (B1 ctx α) (B2 ctx α) (Priority × α) Unit α Unit :=
  newConvergentSREvent' B1.Put.toConvergentEvent.toOrdinaryEvent {
    guard := fun b2 _ => b2.data.length < ctx.maxSize
    action := fun b2 (p, x) => { data := (p,x) :: b2.data }
    lift_in := fun (_, x) => x
    safety := fun b2 (p, x) => by
      simp [Machine.invariant]
      intros _ Hgrd
      linarith
    strengthening := fun b2 _ => by
      simp [Machine.invariant, B1.Put, FRefinement.lift]
    simulation := fun b2 (_, x) => by
      simp [Machine.invariant, B1.Put, FRefinement.lift]
    variant := fun b2 => ctx.maxSize - b2.data.length
    convergence := fun b2 (p, x) => by
      simp [Machine.invariant]
      intro _
      omega
  }

def B2.Fetch [DecidableEq α] [Inhabited α]: ConvergentRDetEvent Nat (B1 ctx α) (B2 ctx α) Unit α :=
  newConvergentSRDetEvent B1.Fetch.toConvergentNDEvent.toAnticipatedNDEvent.toOrdinaryNDEvent
  {
    guard := fun b2 _ => b2.data.length > 0
    action := fun b2 _ =>
      match b2.data with
      | [] => (default, b2)
      | (_, x)::xs => (x, { data := xs })

    safety := fun b2 x => by
      simp [Machine.invariant]
      split
      case _ _ Heq =>
        simp [Heq]
      case _ x xs Heq =>
        simp [Heq]
        intro H ; exact Nat.le_of_succ_le H

    lift_in := id
    lift_out := id

    strengthening := fun b2 _ => by
      simp [Machine.invariant, B1.Fetch, Refinement.refine]

    simulation := fun b2 _ => by
      simp [Machine.invariant, B1.Fetch, Refinement.refine]
      split <;> simp [*]

    variant := fun b2 => b2.data.length

    convergence := fun b2 _ => by
      simp [Machine.invariant]
      split <;> simp [*]

  }

/-
def B2.FetchPrio [DecidableEq α] : ConvergentREvent Nat (B1 ctx α) (B2 ctx α) Priority (Option α) :=
  newConcreteSREvent {
    guard := fun _ _ => True
  }
-/
end Buffer
