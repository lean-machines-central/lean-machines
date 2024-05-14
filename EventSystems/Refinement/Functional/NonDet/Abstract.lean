
/-
  Reuse of abstract events (functional refinement)
-/

import EventSystems.Refinement.Functional.NonDet.Basic
import EventSystems.Refinement.Functional.Abstract
import EventSystems.Refinement.Relational.NonDet.Abstract

open Refinement
open FRefinement

structure AbstractFRNDEventSpec (AM) [Machine ACTX AM]
                             (M) [Machine CTX M]
                             [FRefinement AM M]
  {α β} (abstract : _NDEvent AM α β)
          extends _AbstractFREventSpec AM M α where

  step_ref (m : M) (x : α):
    Machine.invariant m
    → abstract.guard (lift m) x
    → ∀ y, ∀ am', abstract.effect (lift m) x (y, am')
                  → refine am' (unlift (lift m) am' m x)

  step_safe (m : M) (x : α):
    Machine.invariant m
    → abstract.guard (lift m) x
    → ∀ y, ∀ am', abstract.effect (lift m) x (y, am')
                  → Machine.invariant (unlift (lift m) am' m x)

  lift_unlift (m : M) (am am' : AM) (x : α):
    Machine.invariant m → Machine.invariant am'
    → lift (unlift am am' m x) = am'

@[simp]
def AbstractFRNDEventSpec.toAbstractRNDEventSpec [Machine ACTX AM] [Machine CTX M] [instFR: FRefinement AM M]
  (abs : _NDEvent AM α β) (ev : AbstractFRNDEventSpec AM M abs) : AbstractRNDEventSpec AM M abs :=
  {
    to_AbstractREventSpec := ev.to_AbstractREventSpec
    step_ref := ev.step_ref
    step_safe := ev.step_safe
    lift_unlift := ev.lift_unlift
  }

@[simp]
def newAbstractFRNDEvent [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : OrdinaryNDEvent AM α β) (ev : AbstractFRNDEventSpec AM M abs.to_NDEvent) : OrdinaryRNDEvent AM M α β :=
  newAbstractRNDEvent abs ev.toAbstractRNDEventSpec

@[simp]
def newAbstractAnticipatedFRNDEvent [Preorder v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : AnticipatedNDEvent v AM α β) (ev : AbstractFRNDEventSpec AM M abs.to_NDEvent) : AnticipatedRNDEvent v AM M α β :=
  newAbstractAnticipatedRNDEvent abs ev.toAbstractRNDEventSpec

@[simp]
def newAbstractConvergentFRNDEvent [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : ConvergentNDEvent v AM α β) (ev : AbstractFRNDEventSpec AM M abs.to_NDEvent) : ConvergentRNDEvent v AM M α β :=
  newAbstractConvergentRNDEvent abs ev.toAbstractRNDEventSpec
