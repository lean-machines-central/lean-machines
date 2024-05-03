
/-
  Reuse of abstract events (functional refinement)
-/

import EventSystems.Refinement.Functional.NonDet.Basic
import EventSystems.Refinement.Relational.NonDet.Abstract

open Refinement
open FRefinement

structure _AbstractFRNDEventSpec (AM) [Machine ACTX AM]
                                 (M) [Machine CTX M]
                                 [FRefinement AM M] (α) where

  unlift (am am' : AM) (m : M) (x : α): M

@[simp]
def _AbstractFRNDEventSpec.to_AbstractREventSpec [Machine ACTX AM] [Machine CTX M] [instFR: FRefinement AM M]
  (ev : _AbstractFRNDEventSpec AM M α) : _AbstractREventSpec AM M α :=
  {
    lift := lift
    lift_ref := lift_ref
    refine_uniq := refine_uniq
    unlift := ev.unlift
  }

structure AbstractFRNDEventSpec (AM) [Machine ACTX AM]
                             (M) [Machine CTX M]
                            [FRefinement AM M] (α) (β)
          extends _AbstractFRNDEventSpec AM M α where

  event : OrdinaryNDEvent AM α β

  step_ref (m : M) (x : α):
    Machine.invariant m
    → event.guard (lift m) x
    → ∀ y, ∀ am', event.effect (lift m) x (y, am')
                  → refine am' (unlift (lift m) am' m x)

  step_safe (m : M) (x : α):
    Machine.invariant m
    → event.guard (lift m) x
    → ∀ y, ∀ am', event.effect (lift m) x (y, am')
                  → Machine.invariant (unlift (lift m) am' m x)

  lift_unlift (m : M) (am am' : AM) (x : α):
    Machine.invariant m → Machine.invariant am'
    → lift (unlift am am' m x) = am'

@[simp]
def AbstractFRNDEventSpec.toAbstractRNDEventSpec [Machine ACTX AM] [Machine CTX M] [instFR: FRefinement AM M]
  (ev : AbstractFRNDEventSpec AM M α β) : AbstractRNDEventSpec AM M α β :=
  {
    to_AbstractREventSpec := ev.to_AbstractREventSpec
    event := ev.event
    step_ref := ev.step_ref
    step_safe := ev.step_safe
    lift_unlift := ev.lift_unlift
  }

@[simp]
def newAbstractFRNDEvent [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : AbstractFRNDEventSpec AM M α β) : OrdinaryRNDEvent AM M α β :=
  newAbstractRNDEvent abs.toAbstractRNDEventSpec

structure AbstractFRNDEventSpec' (AM) [Machine ACTX AM]
                             (M) [Machine CTX M]
                            [FRefinement AM M] (α)
          extends _AbstractFRNDEventSpec AM M α where

  event : OrdinaryNDEvent AM α Unit

  step_ref (m : M) (x : α):
    Machine.invariant m
    → event.guard (lift m) x
    → ∀ am', event.effect (lift m) x ((), am')
             → refine am' (unlift (lift m) am' m x)

  step_safe (m : M) (x : α):
    Machine.invariant m
    → event.guard (lift m) x
    → ∀ am', event.effect (lift m) x ((), am')
             → Machine.invariant (unlift (lift m) am' m x)

  lift_unlift (m : M) (am am' : AM) (x : α):
    Machine.invariant m → Machine.invariant am'
    → lift (unlift am am' m x) = am'

@[simp]
def AbstractFRNDEventSpec'.toAbstractFRNDEventSpec [Machine ACTX AM] [Machine CTX M] [instFR: FRefinement AM M]
  (ev : AbstractFRNDEventSpec' AM M α) : AbstractFRNDEventSpec AM M α Unit :=
  {
    to_AbstractFRNDEventSpec := ev.to_AbstractFRNDEventSpec
    event := ev.event
    step_ref := fun m x Hinv Hgrd _ => ev.step_ref m x Hinv Hgrd
    step_safe := fun m x Hinv Hgrd _ => ev.step_safe m x Hinv Hgrd
    lift_unlift := ev.lift_unlift
  }

@[simp]
def newAbstractFRNDEvent' [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : AbstractFRNDEventSpec' AM M α) : OrdinaryRNDEvent AM M α Unit :=
  newAbstractFRNDEvent abs.toAbstractFRNDEventSpec

structure AbstractFRNDEventSpec'' (AM) [Machine ACTX AM]
                             (M) [Machine CTX M]
                            [FRefinement AM M]
          extends _AbstractFRNDEventSpec AM M Unit where

  event : OrdinaryNDEvent AM Unit Unit

  step_ref (m : M):
    Machine.invariant m
    → event.guard (lift m) ()
    → ∀ am', event.effect (lift m) () ((), am')
             → refine am' (unlift (lift m) am' m ())

  step_safe (m : M):
    Machine.invariant m
    → event.guard (lift m) ()
    → ∀ am', event.effect (lift m) () ((), am')
             → Machine.invariant (unlift (lift m) am' m ())

  lift_unlift (m : M) (am am' : AM):
    Machine.invariant m → Machine.invariant am'
    → lift (unlift am am' m ()) = am'

@[simp]
def AbstractFRNDEventSpec''.toAbstractFRNDEventSpec [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : AbstractFRNDEventSpec'' AM M) : AbstractFRNDEventSpec AM M Unit Unit :=
  {
    to_AbstractFRNDEventSpec := ev.to_AbstractFRNDEventSpec
    event := ev.event
    step_ref := fun m _ Hinv Hgrd _ => ev.step_ref m Hinv Hgrd
    step_safe := fun m _ Hinv Hgrd _ => ev.step_safe m Hinv Hgrd
    lift_unlift := fun m am am' _ => ev.lift_unlift m am am'
  }

@[simp]
def newAbstractFRNDEvent'' [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : AbstractFRNDEventSpec'' AM M) : OrdinaryRNDEvent AM M Unit Unit :=
  newAbstractFRNDEvent abs.toAbstractFRNDEventSpec

structure AbstractAnticipatedFRNDEventSpec
              (v) [Preorder v]
              (AM) [Machine ACTX AM]
              (M) [Machine CTX M]
              [FRefinement AM M] (α) (β)
          extends _AbstractFRNDEventSpec AM M α where

  event : AnticipatedNDEvent v AM α β

  step_ref (m : M) (x : α):
    Machine.invariant m
    → event.guard (lift m) x
    → ∀ y, ∀ am', event.effect (lift m) x (y, am')
                  → refine am' (unlift (lift m) am' m x)

  step_safe (m : M) (x : α):
    Machine.invariant m
    → event.guard (lift m) x
    → ∀ y, ∀ am', event.effect (lift m) x (y, am')
                  → Machine.invariant (unlift (lift m) am' m x)

  lift_unlift (m : M) (am am' : AM) (x : α):
    Machine.invariant m → Machine.invariant am'
    → lift (unlift am am' m x) = am'

@[simp]
def AbstractAnticipatedFRNDEventSpec.toAbstractAnticipatedRNDEventSpec [Preorder v] [Machine ACTX AM] [Machine CTX M] [instFR: FRefinement AM M]
  (ev : AbstractAnticipatedFRNDEventSpec v AM M α β) : AbstractAnticipatedRNDEventSpec v AM M α β :=
  {
    to_AbstractREventSpec := ev.to_AbstractREventSpec
    event := ev.event
    step_ref := ev.step_ref
    step_safe := ev.step_safe
    lift_unlift := ev.lift_unlift
  }

@[simp]
def newAbstractAnticipatedFRNDEvent [Preorder v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : AbstractAnticipatedFRNDEventSpec v AM M α β) : AnticipatedRNDEvent v AM M α β :=
  newAbstractAnticipatedRNDEvent abs.toAbstractAnticipatedRNDEventSpec

structure AbstractAnticipatedFRNDEventSpec'
              (v) [Preorder v]
              (AM) [Machine ACTX AM]
              (M) [Machine CTX M]
              [FRefinement AM M] (α)
          extends _AbstractFRNDEventSpec AM M α where

  event : AnticipatedNDEvent v AM α Unit

  step_ref (m : M) (x : α):
    Machine.invariant m
    → event.guard (lift m) x
    → ∀ am', event.effect (lift m) x ((), am')
              → refine am' (unlift (lift m) am' m x)

  step_safe (m : M) (x : α):
    Machine.invariant m
    → event.guard (lift m) x
    → ∀ am', event.effect (lift m) x ((), am')
             → Machine.invariant (unlift (lift m) am' m x)

  lift_unlift (m : M) (am am' : AM) (x : α):
    Machine.invariant m → Machine.invariant am'
    → lift (unlift am am' m x) = am'

@[simp]
def AbstractAnticipatedFRNDEventSpec'.toAbstractAnticipatedFRNDEventSpec [Preorder v] [Machine ACTX AM] [Machine CTX M] [instFR: FRefinement AM M]
  (ev : AbstractAnticipatedFRNDEventSpec' v AM M α) : AbstractAnticipatedFRNDEventSpec v AM M α Unit :=
  {
    to_AbstractFRNDEventSpec := ev.to_AbstractFRNDEventSpec
    event := ev.event
    step_ref := fun m x Hinv Hgrd _ => ev.step_ref m x Hinv Hgrd
    step_safe := fun m x Hinv Hgrd _ => ev.step_safe m x Hinv Hgrd
    lift_unlift := ev.lift_unlift
  }

@[simp]
def newAbstractAnticipatedFRNDEvent' [Preorder v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : AbstractAnticipatedFRNDEventSpec' v AM M α) : AnticipatedRNDEvent v AM M α Unit :=
  newAbstractAnticipatedFRNDEvent abs.toAbstractAnticipatedFRNDEventSpec

structure AbstractAnticipatedFRNDEventSpec''
              (v) [Preorder v]
              (AM) [Machine ACTX AM]
              (M) [Machine CTX M]
              [FRefinement AM M]
          extends _AbstractFRNDEventSpec AM M Unit where

  event : AnticipatedNDEvent v AM Unit Unit

  step_ref (m : M):
    Machine.invariant m
    → event.guard (lift m) ()
    → ∀ am', event.effect (lift m) () ((), am')
              → refine am' (unlift (lift m) am' m ())

  step_safe (m : M):
    Machine.invariant m
    → event.guard (lift m) ()
    → ∀ am', event.effect (lift m) () ((), am')
             → Machine.invariant (unlift (lift m) am' m ())

  lift_unlift (m : M) (am am' : AM):
    Machine.invariant m → Machine.invariant am'
    → lift (unlift am am' m ()) = am'

@[simp]
def AbstractAnticipatedFRNDEventSpec''.toAbstractAnticipatedFRNDEventSpec [Preorder v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : AbstractAnticipatedFRNDEventSpec'' v AM M) : AbstractAnticipatedFRNDEventSpec v AM M Unit Unit :=
  {
    to_AbstractFRNDEventSpec := ev.to_AbstractFRNDEventSpec
    event := ev.event
    step_ref := fun m _ Hinv Hgrd _ => ev.step_ref m Hinv Hgrd
    step_safe := fun m _ Hinv Hgrd _ => ev.step_safe m Hinv Hgrd
    lift_unlift := fun m am' am _ => ev.lift_unlift m am' am
  }

@[simp]
def newAbstractAnticipatedFRNDEvent'' [Preorder v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : AbstractAnticipatedFRNDEventSpec'' v AM M) : AnticipatedRNDEvent v AM M Unit Unit :=
  newAbstractAnticipatedFRNDEvent abs.toAbstractAnticipatedFRNDEventSpec

structure AbstractConvergentFRNDEventSpec
              (v) [Preorder v] [WellFoundedLT v]
              (AM) [Machine ACTX AM]
              (M) [Machine CTX M]
              [FRefinement AM M] (α) (β)
          extends _AbstractFRNDEventSpec AM M α where

  event : ConvergentNDEvent v AM α β

  step_ref (m : M) (x : α):
    Machine.invariant m
    → event.guard (lift m) x
    → ∀ y, ∀ am', event.effect (lift m) x (y, am')
                  → refine am' (unlift (lift m) am' m x)

  step_safe (m : M) (x : α):
    Machine.invariant m
    → event.guard (lift m) x
    → ∀ y, ∀ am', event.effect (lift m) x (y, am')
                  → Machine.invariant (unlift (lift m) am' m x)

  lift_unlift (m : M) (am am' : AM) (x : α):
    Machine.invariant m → Machine.invariant am'
    → lift (unlift am am' m x) = am'

@[simp]
def AbstractConvergentFRNDEventSpec.toAbstractConvergentRNDEventSpec [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [instFR: FRefinement AM M]
  (ev : AbstractConvergentFRNDEventSpec v AM M α β) : AbstractConvergentRNDEventSpec v AM M α β :=
  {
    to_AbstractREventSpec := ev.to_AbstractREventSpec
    event := ev.event
    step_ref := ev.step_ref
    step_safe := ev.step_safe
    lift_unlift := ev.lift_unlift
  }

@[simp]
def newAbstractConvergentFRNDEvent [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : AbstractConvergentFRNDEventSpec v AM M α β) : ConvergentRNDEvent v AM M α β :=
  newAbstractConvergentRNDEvent abs.toAbstractConvergentRNDEventSpec

structure AbstractConvergentFRNDEventSpec'
              (v) [Preorder v] [WellFoundedLT v]
              (AM) [Machine ACTX AM]
              (M) [Machine CTX M]
              [FRefinement AM M] (α)
          extends _AbstractFRNDEventSpec AM M α where

  event : ConvergentNDEvent v AM α Unit

  step_ref (m : M) (x : α):
    Machine.invariant m
    → event.guard (lift m) x
    → ∀ am', event.effect (lift m) x ((), am')
              → refine am' (unlift (lift m) am' m x)

  step_safe (m : M) (x : α):
    Machine.invariant m
    → event.guard (lift m) x
    → ∀ am', event.effect (lift m) x ((), am')
             → Machine.invariant (unlift (lift m) am' m x)

  lift_unlift (m : M) (am am' : AM) (x : α):
    Machine.invariant m → Machine.invariant am'
    → lift (unlift am am' m x) = am'

@[simp]
def AbstractConvergentFRNDEventSpec'.toAbstractConvergentFRNDEventSpec [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [instFR: FRefinement AM M]
  (ev : AbstractConvergentFRNDEventSpec' v AM M α) : AbstractConvergentFRNDEventSpec v AM M α Unit :=
  {
    to_AbstractFRNDEventSpec := ev.to_AbstractFRNDEventSpec
    event := ev.event
    step_ref := fun m x Hinv Hgrd _ => ev.step_ref m x Hinv Hgrd
    step_safe := fun m x Hinv Hgrd _ => ev.step_safe m x Hinv Hgrd
    lift_unlift := ev.lift_unlift
  }

@[simp]
def newAbstractConvergentFRNDEvent' [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : AbstractConvergentFRNDEventSpec' v AM M α) : ConvergentRNDEvent v AM M α Unit :=
  newAbstractConvergentFRNDEvent abs.toAbstractConvergentFRNDEventSpec

structure AbstractConvergentFRNDEventSpec''
              (v) [Preorder v] [WellFoundedLT v]
              (AM) [Machine ACTX AM]
              (M) [Machine CTX M]
              [FRefinement AM M]
          extends _AbstractFRNDEventSpec AM M Unit where

  event : ConvergentNDEvent v AM Unit Unit

  step_ref (m : M):
    Machine.invariant m
    → event.guard (lift m) ()
    → ∀ am', event.effect (lift m) () ((), am')
              → refine am' (unlift (lift m) am' m ())

  step_safe (m : M):
    Machine.invariant m
    → event.guard (lift m) ()
    → ∀ am', event.effect (lift m) () ((), am')
             → Machine.invariant (unlift (lift m) am' m ())

  lift_unlift (m : M) (am am' : AM):
    Machine.invariant m → Machine.invariant am'
    → lift (unlift am am' m ()) = am'

@[simp]
def AbstractConvergentFRNDEventSpec''.toAbstractConvergentFRNDEventSpec [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (ev : AbstractConvergentFRNDEventSpec'' v AM M) : AbstractConvergentFRNDEventSpec v AM M Unit Unit :=
  {
    to_AbstractFRNDEventSpec := ev.to_AbstractFRNDEventSpec
    event := ev.event
    step_ref := fun m _ Hinv Hgrd _ => ev.step_ref m Hinv Hgrd
    step_safe := fun m _ Hinv Hgrd _ => ev.step_safe m Hinv Hgrd
    lift_unlift := fun m am' am _ => ev.lift_unlift m am' am
  }

@[simp]
def newAbstractConvergentFRNDEvent'' [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [FRefinement AM M]
  (abs : AbstractConvergentFRNDEventSpec'' v AM M) : ConvergentRNDEvent v AM M Unit Unit :=
  newAbstractConvergentFRNDEvent abs.toAbstractConvergentFRNDEventSpec
