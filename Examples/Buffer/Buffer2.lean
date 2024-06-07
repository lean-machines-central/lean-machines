

import Mathlib.Tactic

import LeanMachines.Refinement.Strong.Basic
import LeanMachines.Refinement.Strong.Convergent
import LeanMachines.Refinement.Strong.Abstract
import LeanMachines.Refinement.Strong.Concrete

import LeanMachines.Refinement.Strong.NonDet.Det.Convergent

import Examples.Buffer.Buffer1

namespace Buffer

inductive Priority where
  | Low | Mid | Hi
  deriving DecidableEq

structure B2 (ctx : BufContext) (α : Type) where
  data : List (Priority × α)

instance: Machine BufContext (B2 ctx α) where
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

  lift := B2.lift
  lift_safe b2 := by simp [Machine.invariant]

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
      simp [Machine.invariant, B1.Fetch, Refinement.refine, FRefinement.lift]

    simulation := fun b2 _ => by
      simp [Machine.invariant, B1.Fetch, Refinement.refine, FRefinement.lift]
      split <;> simp [*]

    variant := fun b2 => b2.data.length

    convergence := fun b2 _ => by
      simp [Machine.invariant]
      split <;> simp [*]

  }

def removePrio (p : Priority) (xs : List (Priority × α)) : (Option α) × List (Priority × α) :=
  match xs with
  | [] => (none, [])
  | (q,x)::xs => if p = q then (some x, xs)
                 else let (r, xs') := removePrio p xs
                      (r, (q,x)::xs')

theorem removePrio_none_id (p : Priority) (xs : List (Priority × α)):
  ∀ xs', removePrio p xs = (none, xs')
  → xs' = xs :=
by
  induction xs
  case nil =>
    simp [removePrio]
  case cons x xs Hind =>
    simp [removePrio]
    split
    · simp
    case inr Hneq =>
      intros xs' Hrm
      cases xs'
      case nil =>
        simp [removePrio] at Hrm
      case cons x' xs' =>
        have Hrm': x :: (removePrio p xs).2 = x'::xs' := by
          injection Hrm
        have Hx : x' = x := by
          cases Hrm'
          rfl
        rw [Hx] at *
        simp
        apply Hind
        cases Hrm'
        injection Hrm
        case _ H₁ _ =>
          simp [←H₁]


def removePrio_not_some₁ (p : Priority) (xs : List (Priority × α)):
  (∀ val, (removePrio p xs).1 ≠ some val)
  → (removePrio p xs).1 = none :=
by
  exact fun a => (fun {α} {o} => Option.eq_none_iff_forall_not_mem.mpr) a

theorem removePrio_some_cons (p : Priority) (xs xs' : List (Priority × α)) (val : α):
  removePrio p xs = (some val, xs')
  → xs ≠ [] :=
by
  cases xs <;> simp [removePrio]


theorem removePrio_length (p : Priority) (xs : List (Priority × α)):
  match removePrio p xs with
  | (some _, xs') => xs'.length = xs.length - 1
  | (none, xs') => xs'.length = xs.length :=
by
  induction xs
  case nil =>
    simp [removePrio]
  case cons px xs Hind =>
    revert Hind
    split
    case _ _ val xs' Hrm =>
      simp [removePrio]
      rw [Hrm]
      intro Hind
      by_cases p = px.1
      case pos Heq =>
        simp [Heq]
      case neg Hneq =>
        simp [Hneq]
        have Haux : xs ≠ [] := by
          exact removePrio_some_cons p xs xs' val Hrm
        rw [Hind]
        refine Nat.sub_add_cancel ?h
        cases xs
        · contradiction
        exact tsub_add_cancel_iff_le.mp rfl
    case _ xs' Hrm =>
      simp [removePrio]
      rw [Hrm]
      by_cases p = px.1 <;> simp [*]

theorem removePrio_length_some (p : Priority) (xs : List (Priority × α)):
  removePrio p xs = (some x, xs') → xs'.length = xs.length - 1 :=
by
  intro Hrw
  have Hrm := removePrio_length p xs
  simp [Hrw] at Hrm
  assumption

theorem removePrio_length_none (p : Priority) (xs : List (Priority × α)):
  removePrio p xs = (none, xs') → xs'.length = xs.length :=
by
  intro Hrw
  have Hrm := removePrio_length p xs
  simp [Hrw] at Hrm
  assumption


theorem removePrio_mem_some (p : Priority) (xs : List (Priority × α)) (val : α):
  ∀ xs', removePrio p xs = (some val, xs')
  → (p, val) ∈ xs :=
by
  induction xs
  case nil => simp [removePrio]
  case cons x xs Hind =>
    intro xs'
    simp [removePrio]
    split
    case inl Heq =>
      intro Hsome
      cases Hsome
      simp [Heq]
    case inr Hneq =>
      simp
      intros Hrm₁ Hrm₂
      right
      cases xs'
      case nil => contradiction
      case cons x' xs' =>
        have Hrm₂' : x = x' := by
          cases Hrm₂
          rfl
        rw [←Hrm₂'] at Hrm₂
        simp at Hrm₂
        apply Hind xs'
        exact Prod.ext Hrm₁ Hrm₂

theorem removePrio_mem_none (p : Priority) (xs : List (Priority × α)):
  ∀ xs', removePrio p xs = (none, xs')
  → ∀ val, (p, val) ∉ xs :=
by
  induction xs
  case nil => simp [removePrio]
  case cons x xs Hind =>
    simp [removePrio]
    split
    · simp
    case inr Hneq =>
      intros xs' Hrm val
      constructor
      · intro Hfalse
        have Hcontra: p = x.1 := by
          cases Hfalse
          simp
        contradiction
      · cases xs'
        case nil =>
          injection Hrm with Hrm₁ Hrm₂
          injection Hrm₂
        case cons x' xs' =>
          injection Hrm with Hrm₁ Hrm₂
          injection Hrm₂ with Hx Hrm₂
          apply Hind xs'
          exact Prod.ext Hrm₁ Hrm₂

theorem removePrio_mem_none₁ (p : Priority) (xs : List (Priority × α)):
  (removePrio p xs).1 = none
  → ∀ val, (p, val) ∉ xs :=
by
  intros H₁ val
  have Hrm := removePrio_mem_none p xs xs
  apply Hrm
  refine Prod.ext H₁ ?_
  simp
  apply removePrio_none_id p
  exact Prod.fst_eq_iff.mp H₁


def removeByPrio (xs : List (Priority × α)) : (Option α) × List (Priority × α) :=
  match removePrio Priority.Hi xs with
  | (some x, xs') => (some x, xs')
  | _ => match removePrio Priority.Mid xs with
         | (some x, xs') => (some x, xs')
         | _ => match removePrio Priority.Low xs with
                | (some x, xs') => (some x, xs')
                | _ => (none, xs)

theorem removeByPrio_len_some (xs : List (Priority × α)):
  removeByPrio xs = (some x, xs')
  -> xs'.length = xs.length - 1 :=
by
  simp [removeByPrio]
  split
  case _  y ys Heq =>
    intro Heq'
    have Hys : ys = xs' := by
      cases Heq'
      rfl
    rw [Hys] at Heq
    exact removePrio_length_some Priority.Hi xs Heq
  case _ Hrm =>
    clear Hrm
    split
    case _ y ys Hrm =>
      intro Heq
      have Hys : ys = xs' := by
        cases Heq
        rfl
      rw [Hys] at Hrm
      exact removePrio_length_some Priority.Mid xs Hrm
    case _ _ _ Hrm =>
      clear Hrm
      split
      case _ y ys Hrm =>
        intro Heq
        have Hys : ys = xs' := by
          cases Heq
          rfl
        rw [Hys] at Hrm
        exact removePrio_length_some Priority.Low xs Hrm
      case _ _ _ Hrm =>
        clear Hrm
        intro Hcontra
        cases Hcontra

theorem removeByPrio_len_none (xs : List (Priority × α)):
  removeByPrio xs = (none, xs')
  -> xs'.length = xs.length :=
by
  simp [removeByPrio]
  split
  · intro Hcontra ; cases Hcontra
  · split
    · intro Hcontra ; cases Hcontra
    split
    · intro Hcontra ; cases Hcontra
    · intro Heq
      cases Heq
      rfl

theorem removeByPrio_none_id (xs : List (Priority × α)):
  ∀ xs', removeByPrio xs = (none, xs')
  → xs' = xs :=
by
  intros xs'
  simp [removeByPrio]
  split
  · simp
  split
  · simp
  split
  · simp
  intro H
  injection H
  case _ _ H =>
  exact id (Eq.symm H)

 def removeByPrio_not_some₁ (xs : List (Priority × α)):
  (∀ val, (removeByPrio xs).1 ≠ some val)
  → (removeByPrio xs).1 = none :=
by
  exact fun a => (fun {α} {o} => Option.eq_none_iff_forall_not_mem.mpr) a

theorem removeByPrio_mem_some (xs : List (Priority × α)) (val : α):
  ∀ xs', removeByPrio xs = (some val, xs')
  → ∃ p, (p, val) ∈ xs :=
by
  intro xs'
  simp [removeByPrio]
  split
  case _ y ys Hrm =>
    intro Hsome
    exists Priority.Hi
    apply removePrio_mem_some Priority.Hi xs val xs'
    simp [*]
  case _ r Hrm =>
    clear Hrm
    split
    case _ y ys Hrm' =>
      intro Hsome
      exists Priority.Mid
      apply removePrio_mem_some Priority.Mid xs val xs'
      simp [*]
    case _ r Hrm =>
      clear Hrm
      split
      case _ y ys Hrm =>
        intro Hsome
        exists Priority.Low
        apply removePrio_mem_some Priority.Low xs val xs'
        simp [*]
      case _ r Hrm =>
        intro Hcontra
        cases Hcontra

theorem removeByPrio_mem_nil (xs : List (Priority × α)):
  (removeByPrio xs).1 = none
  → xs = [] :=
by
  simp [removeByPrio]
  split
  · simp
  case _ _ H₁ =>
    split
    · simp
    case _ _ H₂ =>
      split
      · simp
      case _ _ H₃ =>
        simp
        have Hrm₁ : (removePrio Priority.Hi xs).1 = none := by
          apply removePrio_not_some₁
          intro val Hcontra
          have H₁' := H₁ val
          rw [←Hcontra] at H₁'
          exact H₁' (removePrio Priority.Hi xs).2 rfl
        have Hrm₁' : ∀ x, (Priority.Hi, x) ∉ xs := by
          exact fun x => removePrio_mem_none₁ Priority.Hi xs Hrm₁ x
        have Hrm₂ : (removePrio Priority.Mid xs).1 = none := by
          apply removePrio_not_some₁
          intro val Hcontra
          have H₂' := H₂ val
          rw [←Hcontra] at H₂'
          exact H₂' (removePrio Priority.Mid xs).2 rfl
        have Hrm₂' : ∀ x, (Priority.Mid, x) ∉ xs := by
          exact fun x => removePrio_mem_none₁ Priority.Mid xs Hrm₂ x
        have Hrm₃ : (removePrio Priority.Low xs).1 = none := by
          apply removePrio_not_some₁
          intro val Hcontra
          have H₃' := H₃ val
          rw [←Hcontra] at H₃'
          exact H₃' (removePrio Priority.Low xs).2 rfl
        have Hrm₃' : ∀ x, (Priority.Low, x) ∉ xs := by
          exact fun x => removePrio_mem_none₁ Priority.Low xs Hrm₃ x
        clear Hrm₁ Hrm₂ Hrm₃
        have Hfo: ∀ p, ∀ x, (p, x) ∉ xs := by
          intros p x Hcontra
          cases p
          · exact Hrm₃' x Hcontra
          · exact Hrm₂' x Hcontra
          exact Hrm₁' x Hcontra
        exact List.eq_nil_iff_forall_not_mem.mpr fun a => Hfo a.1 a.2


def B2.FetchPrio [DecidableEq α] [Inhabited α]: ConvergentRDetEvent Nat (B1 ctx α) (B2 ctx α) Unit α :=
  newConvergentSRDetEvent B1.Fetch.toConvergentNDEvent.toAnticipatedNDEvent.toOrdinaryNDEvent
  {
    guard := fun b2 _ => b2.data.length > 0
    action := fun b2 _ =>
      match removeByPrio b2.data with
      | (some x, xs) => (x, { data := xs })
      | _ => (default, b2)

    safety := fun b2 x => by
      simp [Machine.invariant]
      split
      case _ y ys Hrm =>
        have Hlen : ys.length = b2.data.length - 1 := by
          exact removeByPrio_len_some b2.data Hrm
        intros Hinv _
        simp
        omega
      · intros Hinv _
        simp ; assumption

    lift_in := id
    lift_out := id

    strengthening := fun b2 _ => by
      simp [Machine.invariant, B1.Fetch, Refinement.refine, FRefinement.lift]

    simulation := fun b2 _ => by
      simp [Machine.invariant, B1.Fetch, Refinement.refine, FRefinement.lift]
      split
      case _ y ys Hrm =>
        simp
        have Hlen : ys.length = b2.data.length - 1 := by
          exact removeByPrio_len_some b2.data Hrm
        intros _ _
        constructor
        · exact removeByPrio_mem_some b2.data y ys Hrm
        assumption
      case _ _ _ Hrm =>
        simp
        intro _ Hgrd
        have Hnone: (removeByPrio b2.data).1 = none := by
            refine removeByPrio_not_some₁ b2.data ?_
            intro val
            have Hrm' := Hrm val
            intro Hfalse
            rw [←Hfalse] at Hrm'
            exact
              Hrm'
                (match removePrio Priority.Hi b2.data with
                  | (some x, xs') => (some x, xs')
                  | _ =>
                    match removePrio Priority.Mid b2.data with
                    | (some x, xs') => (some x, xs')
                    | _ =>
                      match removePrio Priority.Low b2.data with
                      | (some x, xs') => (some x, xs')
                      | _ => (none, b2.data)).2
                rfl
        have Hcontra: b2.data = [] := by
            exact removeByPrio_mem_nil b2.data Hnone
        contradiction

    variant := fun b2 => b2.data.length

    convergence := fun b2 _ => by
      simp [Machine.invariant]
      split
      case _ v xs Hrm =>
        intros _ Hgrd
        simp
        have Hlen : xs.length = b2.data.length - 1 := by
          exact removeByPrio_len_some b2.data Hrm
        revert Hgrd
        revert Hlen
        cases b2.data
        case nil => simp
        case cons y ys =>
          intros Hlen _
          rw [Hlen]
          exact Nat.lt.base ((y :: ys).length - 1)
      case _ v xs Hrm =>
        intro _ Hgrd
        have Hnone: (removeByPrio b2.data).1 = none := by
            refine removeByPrio_not_some₁ b2.data ?_
            intro val
            have Hrm' := Hrm val
            intro Hfalse
            rw [←Hfalse] at Hrm'
            exact
              Hrm'
                (match removePrio Priority.Hi b2.data with
                  | (some x, xs') => (some x, xs')
                  | _ =>
                    match removePrio Priority.Mid b2.data with
                    | (some x, xs') => (some x, xs')
                    | _ =>
                      match removePrio Priority.Low b2.data with
                      | (some x, xs') => (some x, xs')
                      | _ => (none, b2.data)).2
                rfl
        have Hcontra: b2.data = [] := by
          exact removeByPrio_mem_nil b2.data Hnone
        contradiction

  }


end Buffer
