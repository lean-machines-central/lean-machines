
/-
  Reuse of abstract events (functional refinement)
-/

import EventSystems.Refinement.Functional.Basic
import EventSystems.Refinement.Functional.Convergent

import EventSystems.Refinement.Relational.Abstract

open Refinement
open FRefinement

structure _AbstractFREventSpec (AM) [Machine ACTX AM]
                              (M) [Machine CTX M]
                              [FRefinement AM M] (α) where

  unlift (am am' : AM) (m : M) (x : α): M

def _AbstractFREventSpec.to_AbstractREventSpec [Machine ACTX AM] [Machine CTX M] [instFR: FRefinement AM M]
  (ev : _AbstractFREventSpec AM M α) : _AbstractREventSpec AM M α :=
  {
    lift := lift
    lift_ref := lift_ref
    refine_uniq := refine_uniq
    unlift := ev.unlift
  }

structure AbstractFREventSpec (AM) [Machine ACTX AM]
                             (M) [Machine CTX M]
                             [FRefinement AM M]
  {α β} (abstract : _Event AM α β)
          extends _AbstractFREventSpec AM M α where

  step_ref (m : M) (x : α):
    Machine.invariant m
    → abstract.guard (lift m) x
    → let (_, am') := abstract.action (lift m) x
      refine am' (unlift (lift m) am' m x)

  step_safe (m : M) (x : α):
    Machine.invariant m
    → abstract.guard (lift m) x
    → let (_, am') := abstract.action (lift m) x
      Machine.invariant am' -- redundant but useful
      → Machine.invariant (unlift (lift m) am' m x)

@[simp]
def AbstractFREventSpec.toAbstractREventSpec [Machine ACTX AM] [Machine CTX M] [instFR: FRefinement AM M]
  (abs : _Event AM α β) (ev : AbstractFREventSpec AM M abs) : AbstractREventSpec AM M abs :=
  {
    to_AbstractREventSpec := ev.to_AbstractREventSpec
    step_ref := ev.step_ref
    step_safe := ev.step_safe
  }

@[simp]
def newAbstractFREvent [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : OrdinaryEvent AM α β) (ev : AbstractFREventSpec AM M abs.to_Event) : OrdinaryREvent AM M α β :=
  newAbstractREvent abs ev.toAbstractREventSpec

structure AbstractAnticipatedFREventSpec
              (v) [Preorder v]
              (AM) [Machine ACTX AM]
              (M) [Machine CTX M]
              [FRefinement AM M]
  {α β} (abstract : AnticipatedEvent v AM α β)
          extends AbstractFREventSpec AM M abstract.to_Event where

  step_variant (m : M) (x : α):
    Machine.invariant m
    → abstract.guard (lift m) x
    → let (_, am') := abstract.action (lift m) x
      Machine.invariant am' -- redundant but useful
      → abstract.po.variant (lift (unlift (lift m) am' m x))
      = abstract.po.variant am'

@[simp]
def AbstractAnticipatedFREventSpec.toAbstractAnticipatedREventSpec [Preorder v] [Machine ACTX AM] [Machine CTX M] [instFR: FRefinement AM M]
  (abs : AnticipatedEvent v AM α β) (ev : AbstractAnticipatedFREventSpec v AM M abs) : AbstractAnticipatedREventSpec v AM M abs :=
  {
    to_AbstractREventSpec := ev.to_AbstractREventSpec
    step_ref := ev.step_ref
    step_safe := ev.step_safe
    step_variant := ev.step_variant
  }

@[simp]
def newAbstractAnticipatedFREvent  [Preorder v] [Machine ACTX AM] [Machine CTX M] [instFR: FRefinement AM M]
  (abs : AnticipatedEvent v AM α β) (ev : AbstractAnticipatedFREventSpec v AM M abs) : AnticipatedREvent v AM M α β :=
  newAbstractAnticipatedREvent abs ev.toAbstractAnticipatedREventSpec

structure AbstractConvergentFREventSpec
              (v) [Preorder v] [WellFoundedLT v]
              (AM) [Machine ACTX AM]
              (M) [Machine CTX M]
              [FRefinement AM M]
  {α β} (abstract : ConvergentEvent v AM α β)
          extends AbstractAnticipatedFREventSpec v AM M abstract.toAnticipatedEvent where

@[simp]
def AbstractConvergentFREventSpec.toAbstractConvergentREventSpec [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [instFR: FRefinement AM M]
  (abs : ConvergentEvent v AM α β) (ev : AbstractConvergentFREventSpec v AM M abs) : AbstractConvergentREventSpec v AM M abs :=
  {
    toAbstractAnticipatedREventSpec := ev.toAbstractAnticipatedREventSpec
  }

@[simp]
def newAbstractConvergentFREvent  [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [instFR: FRefinement AM M]
  (abs : ConvergentEvent v AM α β) (ev : AbstractConvergentFREventSpec v AM M abs) : ConvergentREvent v AM M α β :=
  newAbstractConvergentREvent abs ev.toAbstractConvergentREventSpec
