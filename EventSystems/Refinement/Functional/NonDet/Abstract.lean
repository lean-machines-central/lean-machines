
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

structure AbstractFRNDEventSpec' (AM) [Machine ACTX AM]
                             (M) [Machine CTX M]
                             [FRefinement AM M]
  {α} (abstract : _NDEvent AM α Unit)
          extends _AbstractFREventSpec AM M α where

  step_ref (m : M) (x : α):
    Machine.invariant m
    → abstract.guard (lift m) x
    → ∀ am', abstract.effect (lift m) x ((), am')
             → refine am' (unlift (lift m) am' m x)

  step_safe (m : M) (x : α):
    Machine.invariant m
    → abstract.guard (lift m) x
    → ∀ am', abstract.effect (lift m) x ((), am')
              → Machine.invariant (unlift (lift m) am' m x)

  lift_unlift (m : M) (am am' : AM) (x : α):
    Machine.invariant m → Machine.invariant am'
    → lift (unlift am am' m x) = am'

@[simp]
def AbstractFRNDEventSpec'.toAbstractFRNDEventSpec [Machine ACTX AM] [Machine CTX M] [instFR: FRefinement AM M]
  (abs : _NDEvent AM α Unit) (ev : AbstractFRNDEventSpec' AM M abs) : AbstractFRNDEventSpec AM M abs :=
  {
    to_AbstractFREventSpec := ev.to_AbstractFREventSpec
    step_ref := fun m x => by
      intros Hinv Hgrd y am' Heff
      apply ev.step_ref m x <;> assumption

    step_safe := fun m x => by
      intros Hinv Hgrd y am' Heff
      apply ev.step_safe m x <;> assumption

    lift_unlift := ev.lift_unlift
  }

@[simp]
def newAbstractFRNDEvent' [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : OrdinaryNDEvent AM α Unit) (ev : AbstractFRNDEventSpec' AM M abs.to_NDEvent) : OrdinaryRNDEvent AM M α Unit :=
  newAbstractFRNDEvent abs ev.toAbstractFRNDEventSpec

structure AbstractFRNDEventSpec'' (AM) [Machine ACTX AM]
                             (M) [Machine CTX M]
                             [FRefinement AM M]
  (abstract : _NDEvent AM Unit Unit)
          extends _AbstractFREventSpec'' AM M where

  step_ref (m : M):
    Machine.invariant m
    → abstract.guard (lift m) ()
    → ∀ am', abstract.effect (lift m) () ((), am')
             → refine am' (unlift (lift m) am' m)

  step_safe (m : M):
    Machine.invariant m
    → abstract.guard (lift m) ()
    → ∀ am', abstract.effect (lift m) () ((), am')
              → Machine.invariant (unlift (lift m) am' m)

  lift_unlift (m : M) (am am' : AM):
    Machine.invariant m → Machine.invariant am'
    → lift (unlift am am' m) = am'

@[simp]
def AbstractFRNDEventSpec''.toAbstractFRNDEventSpec [Machine ACTX AM] [Machine CTX M] [instFR: FRefinement AM M]
  (abs : _NDEvent AM Unit Unit) (ev : AbstractFRNDEventSpec'' AM M abs) : AbstractFRNDEventSpec AM M abs :=
  {
    to_AbstractFREventSpec := ev.to_AbstractFREventSpec
    step_ref := fun m x => by
      intros Hinv Hgrd _ am' Heff
      apply ev.step_ref m <;> assumption

    step_safe := fun m x => by
      intros Hinv Hgrd _ am' Heff
      apply ev.step_safe m <;> assumption

    lift_unlift := fun am am' m _ => ev.lift_unlift am am' m
  }

@[simp]
def newAbstractFRNDEvent'' [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : OrdinaryNDEvent AM Unit Unit) (ev : AbstractFRNDEventSpec'' AM M abs.to_NDEvent) : OrdinaryRNDEvent AM M Unit Unit :=
  newAbstractFRNDEvent abs ev.toAbstractFRNDEventSpec

structure AbstractInitFRNDEventSpec (AM) [Machine ACTX AM]
                             (M) [Machine CTX M]
                             [FRefinement AM M]
  {α β} (abstract : _NDEvent AM α β)
          extends _AbstractFREventSpec AM M α where

  step_ref (x : α):
    abstract.guard Machine.reset x
    → ∀ y, ∀ am', abstract.effect Machine.reset x (y, am')
                  → refine am' (unlift Machine.reset am' Machine.reset x)

  step_safe (x : α):
    abstract.guard Machine.reset x
    → ∀ y, ∀ am', abstract.effect Machine.reset x (y, am')
                  → Machine.invariant (unlift Machine.reset am' Machine.reset x)

  lift_unlift (am' : AM) (x : α):
    Machine.invariant am'
    → lift (unlift Machine.reset am' Machine.reset x) = am'

@[simp]
def AbstractInitFRNDEventSpec.toAbstractInitRNDEventSpec [Machine ACTX AM] [Machine CTX M] [instFR: FRefinement AM M]
  (abs : InitNDEvent AM α β) (ev : AbstractInitFRNDEventSpec AM M abs.to_NDEvent) : AbstractInitRNDEventSpec AM M abs.to_NDEvent :=
  {
    to_AbstractREventSpec := ev.to_AbstractREventSpec
    step_ref := ev.step_ref
    step_safe := ev.step_safe
    lift_unlift := ev.lift_unlift
  }

@[simp]
def newAbstractInitFRNDEvent [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : InitNDEvent AM α β) (ev : AbstractInitFRNDEventSpec AM M abs.to_NDEvent) : InitRNDEvent AM M α β :=
  newAbstractInitRNDEvent abs ev.toAbstractInitRNDEventSpec


@[simp]
def newAbstractAnticipatedFRNDEvent [Preorder v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : AnticipatedNDEvent v AM α β) (ev : AbstractFRNDEventSpec AM M abs.to_NDEvent) : AnticipatedRNDEvent v AM M α β :=
  newAbstractAnticipatedRNDEvent abs ev.toAbstractRNDEventSpec

@[simp]
def newAbstractConvergentFRNDEvent [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : ConvergentNDEvent v AM α β) (ev : AbstractFRNDEventSpec AM M abs.to_NDEvent) : ConvergentRNDEvent v AM M α β :=
  newAbstractConvergentRNDEvent abs ev.toAbstractRNDEventSpec
