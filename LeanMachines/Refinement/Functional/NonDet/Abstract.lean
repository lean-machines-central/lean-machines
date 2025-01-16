
/-
  Reuse of abstract events (functional refinement)
-/

import LeanMachines.Refinement.Functional.NonDet.Basic
import LeanMachines.Refinement.Functional.Abstract
import LeanMachines.Refinement.Relational.NonDet.Abstract

open Refinement
open FRefinement

structure AbstractFRNDEventSpec (AM) [@Machine ACTX AM]
                             (M) [@Machine CTX M]
                             [FRefinement AM M]
  {α β} (abstract : OrdinaryNDEvent AM α β)
          extends _AbstractFREventSpec AM M α where

  step_ref (m : M) (x : α):
    Machine.invariant m
    → (agrd : abstract.guard (lift m) x)
    → ∀ y, ∀ am', abstract.effect (lift m) x agrd (y, am')
                  → refine am' (unlift (lift m) am' m x)

  step_safe (m : M) (x : α):
    Machine.invariant m
    → (agrd : abstract.guard (lift m) x)
    → ∀ y, ∀ am', abstract.effect (lift m) x agrd (y, am')
                  → Machine.invariant (unlift (lift m) am' m x)

  lift_unlift (m : M) (am am' : AM) (x : α):
    Machine.invariant m → Machine.invariant am'
    → lift (unlift am am' m x) = am'

@[simp]
def AbstractFRNDEventSpec.toAbstractRNDEventSpec [@Machine ACTX AM] [@Machine CTX M] [FRefinement AM M]
  (abs : OrdinaryNDEvent AM α β) (ev : AbstractFRNDEventSpec AM M abs) : AbstractRNDEventSpec AM M abs :=
  {
    to_AbstractREventSpec := ev.to_AbstractREventSpec
    step_ref := ev.step_ref
    step_safe := ev.step_safe
    lift_unlift := ev.lift_unlift
  }

@[simp]
def newAbstractFRNDEvent [@Machine ACTX AM] [@Machine CTX M] [FRefinement AM M]
  (abs : OrdinaryNDEvent AM α β) (ev : AbstractFRNDEventSpec AM M abs) : OrdinaryRNDEvent AM M α β :=
  newAbstractRNDEvent abs ev.toAbstractRNDEventSpec

structure AbstractFRNDEventSpec' (AM) [@Machine ACTX AM]
                             (M) [@Machine CTX M]
                             [FRefinement AM M]
  {α} (abstract : OrdinaryNDEvent AM α Unit)
          extends _AbstractFREventSpec AM M α where

  step_ref (m : M) (x : α):
    Machine.invariant m
    → (agrd : abstract.guard (lift m) x)
    → ∀ am', abstract.effect (lift m) x agrd ((), am')
             → refine am' (unlift (lift m) am' m x)

  step_safe (m : M) (x : α):
    Machine.invariant m
    → (agrd : abstract.guard (lift m) x)
    → ∀ am', abstract.effect (lift m) x agrd ((), am')
              → Machine.invariant (unlift (lift m) am' m x)

  lift_unlift (m : M) (am am' : AM) (x : α):
    Machine.invariant m → Machine.invariant am'
    → lift (unlift am am' m x) = am'

@[simp]
def AbstractFRNDEventSpec'.toAbstractFRNDEventSpec [@Machine ACTX AM] [@Machine CTX M] [instFR: FRefinement AM M]
  (abs : OrdinaryNDEvent AM α Unit) (ev : AbstractFRNDEventSpec' AM M abs) : AbstractFRNDEventSpec AM M abs :=
  {
    to_AbstractFREventSpec := ev.to_AbstractFREventSpec
    step_ref := fun m x => by
      intros Hinv Hgrd _ am' Heff
      apply ev.step_ref m x <;> assumption

    step_safe := fun m x => by
      intros Hinv Hgrd _ am' Heff
      apply ev.step_safe m x <;> assumption

    lift_unlift := ev.lift_unlift
  }

@[simp]
def newAbstractFRNDEvent' [@Machine ACTX AM] [@Machine CTX M] [FRefinement AM M]
  (abs : OrdinaryNDEvent AM α Unit) (ev : AbstractFRNDEventSpec' AM M abs) : OrdinaryRNDEvent AM M α Unit :=
  newAbstractFRNDEvent abs ev.toAbstractFRNDEventSpec

structure AbstractFRNDEventSpec'' (AM) [@Machine ACTX AM]
                             (M) [@Machine CTX M]
                             [FRefinement AM M]
  (abstract : OrdinaryNDEvent AM Unit Unit)
          extends _AbstractFREventSpec'' AM M where

  step_ref (m : M):
    Machine.invariant m
    → (agrd : abstract.guard (lift m) ())
    → ∀ am', abstract.effect (lift m) () agrd ((), am')
             → refine am' (unlift (lift m) am' m)

  step_safe (m : M):
    Machine.invariant m
    → (agrd : abstract.guard (lift m) ())
    → ∀ am', abstract.effect (lift m) () agrd ((), am')
              → Machine.invariant (unlift (lift m) am' m)

  lift_unlift (m : M) (am am' : AM):
    Machine.invariant m → Machine.invariant am'
    → lift (unlift am am' m) = am'

@[simp]
def AbstractFRNDEventSpec''.toAbstractFRNDEventSpec [@Machine ACTX AM] [@Machine CTX M] [instFR: FRefinement AM M]
  (abs : OrdinaryNDEvent AM Unit Unit) (ev : AbstractFRNDEventSpec'' AM M abs) : AbstractFRNDEventSpec AM M abs :=
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
def newAbstractFRNDEvent'' [@Machine ACTX AM] [@Machine CTX M] [FRefinement AM M]
  (abs : OrdinaryNDEvent AM Unit Unit) (ev : AbstractFRNDEventSpec'' AM M abs) : OrdinaryRNDEvent AM M Unit Unit :=
  newAbstractFRNDEvent abs ev.toAbstractFRNDEventSpec

structure AbstractInitFRNDEventSpec (AM) [@Machine ACTX AM]
                             (M) [@Machine CTX M]
                             [FRefinement AM M]
  {α β} (abstract : InitNDEvent AM α β)
          extends _AbstractFREventSpec AM M α where

  step_ref (x : α):
    (agrd : abstract.guard x)
    → ∀ y, ∀ am', abstract.init x agrd (y, am')
                  → refine am' (unlift default am' default x)

  step_safe (x : α):
    (agrd : abstract.guard x)
    → ∀ y, ∀ am', abstract.init x agrd (y, am')
                  → Machine.invariant (unlift default am' default x)

  lift_unlift (am' : AM) (x : α):
    Machine.invariant am'
    → lift (unlift default am' default x) = am'

@[simp]
def AbstractInitFRNDEventSpec.toAbstractInitRNDEventSpec [@Machine ACTX AM] [@Machine CTX M] [FRefinement AM M]
  (abs : InitNDEvent AM α β) (ev : AbstractInitFRNDEventSpec AM M abs) : AbstractInitRNDEventSpec AM M abs :=
  {
    to_AbstractREventSpec := ev.to_AbstractREventSpec
    step_ref := ev.step_ref
    step_safe := ev.step_safe
    lift_unlift := ev.lift_unlift
  }

@[simp]
def newAbstractInitFRNDEvent [@Machine ACTX AM] [@Machine CTX M] [FRefinement AM M]
  (abs : InitNDEvent AM α β) (ev : AbstractInitFRNDEventSpec AM M abs) : InitRNDEvent AM M α β :=
  newAbstractInitRNDEvent abs ev.toAbstractInitRNDEventSpec

structure AbstractInitFRNDEventSpec' (AM) [@Machine ACTX AM]
                             (M) [@Machine CTX M]
                             [FRefinement AM M]
  {α} (abstract : InitNDEvent AM α Unit)
          extends _AbstractFREventSpec AM M α where

  step_ref (x : α):
    (agrd : abstract.guard x)
    → ∀ am', abstract.init x agrd ((), am')
             → refine am' (unlift default am' default x)

  step_safe (x : α):
    (agrd : abstract.guard x)
    → ∀ am', abstract.init x agrd ((), am')
             → Machine.invariant (unlift default am' default x)

  lift_unlift (am' : AM) (x : α):
    Machine.invariant am'
    → lift (unlift default am' default x) = am'

@[simp]
def AbstractInitFRNDEventSpec'.toAbstractInitFRNDEventSpec [@Machine ACTX AM] [@Machine CTX M] [instFR: FRefinement AM M]
  (abs : InitNDEvent AM α Unit) (ev : AbstractInitFRNDEventSpec' AM M abs) : AbstractInitFRNDEventSpec AM M abs :=
  {
    to_AbstractFREventSpec := ev.to_AbstractFREventSpec
    step_ref := fun x => by
      intros Hgrd _ am' Hini
      apply ev.step_ref x <;> assumption

    step_safe := fun x => by
      intros Hgrd _ am' Hini
      apply ev.step_safe x <;> assumption

    lift_unlift := ev.lift_unlift
  }

@[simp]
def newAbstractInitFRNDEvent' [@Machine ACTX AM] [@Machine CTX M] [FRefinement AM M]
  (abs : InitNDEvent AM α Unit) (ev : AbstractInitFRNDEventSpec' AM M abs) : InitRNDEvent AM M α Unit :=
  newAbstractInitFRNDEvent abs ev.toAbstractInitFRNDEventSpec

structure AbstractInitFRNDEventSpec'' (AM) [@Machine ACTX AM]
                             (M) [@Machine CTX M]
                             [FRefinement AM M]
  (abstract : InitNDEvent AM Unit Unit)
          extends _AbstractFREventSpec'' AM M where

  step_ref:
    (agrd : abstract.guard ())
    → ∀ am', abstract.init () agrd ((), am')
             → refine am' (unlift default am' default)

  step_safe:
    (agrd : abstract.guard ())
    → ∀ am', abstract.init () agrd ((), am')
             → Machine.invariant (unlift default am' default)

  lift_unlift (am' : AM):
    Machine.invariant am'
    → lift (unlift default am' default) = am'

@[simp]
def AbstractInitFRNDEventSpec''.toAbstractInitFRNDEventSpec [@Machine ACTX AM] [@Machine CTX M] [instFR: FRefinement AM M]
  (abs : InitNDEvent AM Unit Unit) (ev : AbstractInitFRNDEventSpec'' AM M abs) : AbstractInitFRNDEventSpec AM M abs :=
  {
    to_AbstractFREventSpec := ev.to_AbstractFREventSpec
    step_ref := fun () => by
      intros Hgrd _ am' Hini
      apply ev.step_ref <;> assumption

    step_safe := fun () => by
      intros Hgrd _ am' Hini
      apply ev.step_safe <;> assumption

    lift_unlift := fun am' () => ev.lift_unlift am'
  }

@[simp]
def newAbstractInitFRNDEvent'' [@Machine ACTX AM] [@Machine CTX M] [FRefinement AM M]
  (abs : InitNDEvent AM Unit Unit) (ev : AbstractInitFRNDEventSpec'' AM M abs) : InitRNDEvent AM M Unit Unit :=
  newAbstractInitFRNDEvent abs ev.toAbstractInitFRNDEventSpec

@[simp]
def newAbstractAnticipatedFRNDEvent [Preorder v] [@Machine ACTX AM] [@Machine CTX M] [FRefinement AM M]
  (abs : AnticipatedNDEvent v AM α β) (ev : AbstractFRNDEventSpec AM M abs.toOrdinaryNDEvent) : AnticipatedRNDEvent v AM M α β :=
  newAbstractAnticipatedRNDEvent abs ev.toAbstractRNDEventSpec

@[simp]
def newAbstractAnticipatedFRNDEvent' [Preorder v] [@Machine ACTX AM] [@Machine CTX M] [FRefinement AM M]
  (abs : AnticipatedNDEvent v AM α Unit) (ev : AbstractFRNDEventSpec' AM M abs.toOrdinaryNDEvent) : AnticipatedRNDEvent v AM M α Unit :=
  newAbstractAnticipatedFRNDEvent abs ev.toAbstractFRNDEventSpec

@[simp]
def newAbstractAnticipatedFRNDEvent'' [Preorder v] [@Machine ACTX AM] [@Machine CTX M] [FRefinement AM M]
  (abs : AnticipatedNDEvent v AM Unit Unit) (ev : AbstractFRNDEventSpec'' AM M abs.toOrdinaryNDEvent) : AnticipatedRNDEvent v AM M Unit Unit :=
  newAbstractAnticipatedFRNDEvent abs ev.toAbstractFRNDEventSpec

@[simp]
def newAbstractConvergentFRNDEvent [Preorder v] [WellFoundedLT v] [@Machine ACTX AM] [@Machine CTX M] [FRefinement AM M]
  (abs : ConvergentNDEvent v AM α β) (ev : AbstractFRNDEventSpec AM M abs.toAnticipatedNDEvent.toOrdinaryNDEvent) : ConvergentRNDEvent v AM M α β :=
  newAbstractConvergentRNDEvent abs ev.toAbstractRNDEventSpec

@[simp]
def newAbstractConvergentFRNDEvent' [Preorder v] [WellFoundedLT v] [@Machine ACTX AM] [@Machine CTX M] [FRefinement AM M]
  (abs : ConvergentNDEvent v AM α Unit) (ev : AbstractFRNDEventSpec' AM M abs.toAnticipatedNDEvent.toOrdinaryNDEvent) : ConvergentRNDEvent v AM M α Unit :=
  newAbstractConvergentFRNDEvent abs ev.toAbstractFRNDEventSpec

@[simp]
def newAbstractConvergentFRNDEvent'' [Preorder v] [WellFoundedLT v] [@Machine ACTX AM] [@Machine CTX M] [FRefinement AM M]
  (abs : ConvergentNDEvent v AM Unit Unit) (ev : AbstractFRNDEventSpec'' AM M abs.toAnticipatedNDEvent.toOrdinaryNDEvent) : ConvergentRNDEvent v AM M Unit Unit :=
  newAbstractConvergentFRNDEvent abs ev.toAbstractFRNDEventSpec
