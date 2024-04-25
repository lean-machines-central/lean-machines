
/-
  Reuse of abstract events (strong refinement)
-/

import EventSystems.Refinement.Strong.Basic
import EventSystems.Refinement.Strong.Convergent

import EventSystems.Refinement.Functional.Abstract

open Refinement
open FRefinement
open SRefinement

structure AbstractSREventSpec (AM) [Machine ACTX AM]
                               (M) [Machine CTX M]
                               [SRefinement AM M] (α) (β) where

  event : OrdinaryEvent AM α β

  step_inv (m : M) (x : α):
    Machine.invariant m
    → event.guard (lift m) x
    → let (_, am') := event.action (lift m) x
      --Machine.invariant am' -- redundant
      --→
      Machine.invariant (unlift m am')

def AbstractSREventSpec.toAbstractFREventSpec [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (ev : AbstractSREventSpec AM M α β) : AbstractFREventSpec AM M α β :=
  {
    event := ev.event
    unlift := fun _ am' m _ => unlift m am'
    step_ref := fun m x => by simp
                              intros Hinv Hgrd
                              have Hsafe := ev.step_inv m x Hinv Hgrd
                              simp at Hsafe
                              apply unlift_refine
                              · intros _ _
                                assumption
                              · assumption
                              have Hls : Machine.invariant (lift m) := lift_safe (AM:=AM) m Hinv
                              apply ev.event.po.safety (lift m) x Hls Hgrd

    step_safe := fun m x => by simp
                               intros Hinv Hgrd _
                               apply ev.step_inv m x Hinv Hgrd
  }

@[simp]
def newAbstractSREvent [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (abs : AbstractSREventSpec AM M α β) : OrdinaryREvent AM M α β :=
  newAbstractFREvent abs.toAbstractFREventSpec

structure AbstractSREventSpec' (AM) [Machine ACTX AM]
                               (M) [Machine CTX M]
                               [SRefinement AM M] (α) where

  event : OrdinaryEvent AM α Unit

  step_inv (m : M) (x : α):
    Machine.invariant m
    → event.guard (lift m) x
    → let (_, am') := event.action (lift m) x
      --Machine.invariant am' -- redundant
      --→
      Machine.invariant (unlift m am')

@[simp]
def AbstractSREventSpec'.toAbstractSREventSpec  [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (ev : AbstractSREventSpec' AM M α) : AbstractSREventSpec AM M α Unit :=
  {
    event := ev.event
    step_inv := ev.step_inv
  }

@[simp]
def newAbstractSREvent' [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (abs : AbstractSREventSpec' AM M α) : OrdinaryREvent AM M α Unit :=
  newAbstractSREvent abs.toAbstractSREventSpec

structure AbstractSREventSpec'' (AM) [Machine ACTX AM]
                                (M) [Machine CTX M]
                                [SRefinement AM M] where

  event : OrdinaryEvent AM Unit Unit

  step_inv (m : M) (x : α):
    Machine.invariant m
    → event.guard (lift m) ()
    → let (_, am') := event.action (lift m) ()
      --Machine.invariant am' -- redundant
      --→
      Machine.invariant (unlift m am')

@[simp]
def AbstractSREventSpec''.toAbstractSREventSpec  [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (ev : AbstractSREventSpec'' AM M) : AbstractSREventSpec AM M Unit Unit :=
  {
    event := ev.event
    step_inv := ev.step_inv
  }

@[simp]
def newAbstractSREvent'' [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (abs : AbstractSREventSpec'' AM M) : OrdinaryREvent AM M Unit Unit :=
  newAbstractSREvent abs.toAbstractSREventSpec
