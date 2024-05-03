
import EventSystems.Refinement.Strong.NonDet.Basic
import EventSystems.Refinement.Functional.NonDet.Abstract

open Refinement
open FRefinement
open SRefinement

structure AbstractSRNDEventSpec (AM) [Machine ACTX AM]
                             (M) [Machine CTX M]
                            [instSR: SRefinement AM M] (α) (β)
           where

  event : OrdinaryNDEvent AM α β

  step_inv (m : M) (x : α):
    Machine.invariant m
    → event.guard (lift m) x
    → ∀ y, ∀ am', event.effect (lift m) x (y, am')
                  → Machine.invariant (unlift m am')

@[simp]
def AbstractSRNDEventSpec.toAbstractFRNDEventSpec  [Machine ACTX AM] [Machine CTX M] [instSR: SRefinement AM M]
  (ev : AbstractSRNDEventSpec AM M α β) : AbstractFRNDEventSpec AM M α β :=
  {
    event := ev.event
    unlift := fun _ am' m _ => SRefinement.unlift m am'

    step_ref := fun m x => by
      simp
      intros Hinv Hgrd y am' Heff
      have Hlr := lift_ref (self:=instSR.toFRefinement) m Hinv
      have Hsafe := refine_safe (self:=instSR.toRefinement) (lift m) m Hinv Hlr
      have Hinv' := ev.event.po.safety (lift m) x Hsafe Hgrd y am' Heff
      refine unlift_refine ?Hsafe Hinv Hinv'
      intros
      exact ev.step_inv m x Hinv Hgrd y am' Heff

    step_safe := fun m x => by
      simp
      intros Hinv Hgrd _ am' Heff
      exact ev.step_inv m x Hinv Hgrd _ am' Heff

    lift_unlift := fun m am am' x => by
      simp
      intros Hinv Hainv'
      apply lift_unlift (self:=instSR) m am' Hinv Hainv'
  }

@[simp]
def newAbstractSRNDEvent [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (ev : AbstractSRNDEventSpec AM M α β) : OrdinaryRNDEvent AM M α β :=
  newAbstractFRNDEvent ev.toAbstractFRNDEventSpec

structure AbstractSRNDEventSpec' (AM) [Machine ACTX AM]
                             (M) [Machine CTX M]
                            [instSR: SRefinement AM M] (α)
           where

  event : OrdinaryNDEvent AM α Unit

  step_inv (m : M) (x : α):
    Machine.invariant m
    → event.guard (lift m) x
    → ∀ am', event.effect (lift m) x ((), am')
             → Machine.invariant (unlift m am')

@[simp]
def AbstractSRNDEventSpec'.toAbstractSRNDEventSpec [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (ev : AbstractSRNDEventSpec' AM M α) : AbstractSRNDEventSpec AM M α Unit :=
  {
    event := ev.event
    step_inv := fun m x Hinv Hgrd _ => ev.step_inv m x Hinv Hgrd
  }

@[simp]
def newAbstractSRNDEvent' [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (ev : AbstractSRNDEventSpec' AM M α) : OrdinaryRNDEvent AM M α Unit :=
  newAbstractSRNDEvent ev.toAbstractSRNDEventSpec

structure AbstractSRNDEventSpec'' (AM) [Machine ACTX AM]
                             (M) [Machine CTX M]
                            [instSR: SRefinement AM M]
           where

  event : OrdinaryNDEvent AM Unit Unit

  step_inv (m : M):
    Machine.invariant m
    → event.guard (lift m) ()
    → ∀ am', event.effect (lift m) () ((), am')
             → Machine.invariant (unlift m am')

@[simp]
def AbstractSRNDEventSpec''.toAbstractSRNDEventSpec [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (ev : AbstractSRNDEventSpec'' AM M) : AbstractSRNDEventSpec AM M Unit Unit :=
  {
    event := ev.event
    step_inv := fun m _ Hinv Hgrd _ => ev.step_inv m Hinv Hgrd
  }

@[simp]
def newAbstractSRNDEvent'' [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (ev : AbstractSRNDEventSpec'' AM M) : OrdinaryRNDEvent AM M Unit Unit :=
  newAbstractSRNDEvent ev.toAbstractSRNDEventSpec

structure AbstractAnticipatedSRNDEventSpec (v) [Preorder v]
                             (AM) [Machine ACTX AM]
                             (M) [Machine CTX M]
                            [instSR: SRefinement AM M] (α) (β)
           where

  event : AnticipatedNDEvent v AM α β

  step_inv (m : M) (x : α):
    Machine.invariant m
    → event.guard (lift m) x
    → ∀ y, ∀ am', event.effect (lift m) x (y, am')
                  → Machine.invariant (unlift m am')

@[simp]
def AbstractAnticipatedSRNDEventSpec.toAbstractAnticipatedFRNDEventSpec [Preorder v] [Machine ACTX AM] [Machine CTX M] [instSR: SRefinement AM M]
  (ev : AbstractAnticipatedSRNDEventSpec v AM M α β) : AbstractAnticipatedFRNDEventSpec v AM M α β :=
  {
    event := ev.event
    unlift := fun _ am' m _ => SRefinement.unlift m am'

    step_ref := fun m x => by
      simp
      intros Hinv Hgrd y am' Heff
      have Hlr := lift_ref (self:=instSR.toFRefinement) m Hinv
      have Hsafe := refine_safe (self:=instSR.toRefinement) (lift m) m Hinv Hlr
      have Hinv' := ev.event.po.safety (lift m) x Hsafe Hgrd y am' Heff
      refine unlift_refine ?Hsafe Hinv Hinv'
      intros
      exact ev.step_inv m x Hinv Hgrd y am' Heff

    step_safe := fun m x => by
      simp
      intros Hinv Hgrd _ am' Heff
      exact ev.step_inv m x Hinv Hgrd _ am' Heff

    lift_unlift := fun m am am' x => by
      simp
      intros Hinv Hainv'
      apply lift_unlift (self:=instSR) m am' Hinv Hainv'
  }

@[simp]
def newAbstractAnticipatedSRNDEvent [Preorder v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (ev : AbstractAnticipatedSRNDEventSpec v AM M α β) : AnticipatedRNDEvent v AM M α β :=
  newAbstractAnticipatedFRNDEvent ev.toAbstractAnticipatedFRNDEventSpec

structure AbstractAnticipatedSRNDEventSpec' (v) [Preorder v]
                             (AM) [Machine ACTX AM]
                             (M) [Machine CTX M]
                            [instSR: SRefinement AM M] (α)
           where

  event : AnticipatedNDEvent v AM α Unit

  step_inv (m : M) (x : α):
    Machine.invariant m
    → event.guard (lift m) x
    → ∀ am', event.effect (lift m) x ((), am')
             → Machine.invariant (unlift m am')

@[simp]
def AbstractAnticipatedSRNDEventSpec'.toAbstractAnticipatedSRNDEventSpec [Preorder v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (ev : AbstractAnticipatedSRNDEventSpec' v AM M α) : AbstractAnticipatedSRNDEventSpec v AM M α Unit :=
  {
    event := ev.event
    step_inv := fun m x Hinv Hgrd _ => ev.step_inv m x Hinv Hgrd
  }

@[simp]
def newAbstractAnticipatedSRNDEvent' [Preorder v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (ev : AbstractAnticipatedSRNDEventSpec' v AM M α) : AnticipatedRNDEvent v AM M α Unit :=
  newAbstractAnticipatedSRNDEvent ev.toAbstractAnticipatedSRNDEventSpec

structure AbstractAnticipatedSRNDEventSpec'' (v) [Preorder v]
                             (AM) [Machine ACTX AM]
                             (M) [Machine CTX M]
                            [instSR: SRefinement AM M]
           where

  event : AnticipatedNDEvent v AM Unit Unit

  step_inv (m : M):
    Machine.invariant m
    → event.guard (lift m) ()
    → ∀ am', event.effect (lift m) () ((), am')
             → Machine.invariant (unlift m am')

@[simp]
def AbstractAnticipatedSRNDEventSpec''.toAbstractAnticipatedSRNDEventSpec [Preorder v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (ev : AbstractAnticipatedSRNDEventSpec'' v AM M) : AbstractAnticipatedSRNDEventSpec v AM M Unit Unit :=
  {
    event := ev.event
    step_inv := fun m _ Hinv Hgrd _ => ev.step_inv m Hinv Hgrd
  }

@[simp]
def newAbstractAnticipatedSRNDEvent'' [Preorder v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (ev : AbstractAnticipatedSRNDEventSpec'' v AM M) : AnticipatedRNDEvent v AM M Unit Unit :=
  newAbstractAnticipatedSRNDEvent ev.toAbstractAnticipatedSRNDEventSpec

structure AbstractConvergentSRNDEventSpec (v) [Preorder v] [WellFoundedLT v]
                             (AM) [Machine ACTX AM]
                             (M) [Machine CTX M]
                            [instSR: SRefinement AM M] (α) (β)
           where

  event : ConvergentNDEvent v AM α β

  step_inv (m : M) (x : α):
    Machine.invariant m
    → event.guard (lift m) x
    → ∀ y, ∀ am', event.effect (lift m) x (y, am')
                  → Machine.invariant (unlift m am')

@[simp]
def AbstractConvergentSRNDEventSpec.toAbstractConvergentFRNDEventSpec [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [instSR: SRefinement AM M]
  (ev : AbstractConvergentSRNDEventSpec v AM M α β) : AbstractConvergentFRNDEventSpec v AM M α β :=
  {
    event := ev.event
    unlift := fun _ am' m _ => SRefinement.unlift m am'

    step_ref := fun m x => by
      simp
      intros Hinv Hgrd y am' Heff
      have Hlr := lift_ref (self:=instSR.toFRefinement) m Hinv
      have Hsafe := refine_safe (self:=instSR.toRefinement) (lift m) m Hinv Hlr
      have Hinv' := ev.event.po.safety (lift m) x Hsafe Hgrd y am' Heff
      refine unlift_refine ?Hsafe Hinv Hinv'
      intros
      exact ev.step_inv m x Hinv Hgrd y am' Heff

    step_safe := fun m x => by
      simp
      intros Hinv Hgrd _ am' Heff
      exact ev.step_inv m x Hinv Hgrd _ am' Heff

    lift_unlift := fun m am am' x => by
      simp
      intros Hinv Hainv'
      apply lift_unlift (self:=instSR) m am' Hinv Hainv'
  }

@[simp]
def newAbstractConvergentSRNDEvent [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (ev : AbstractConvergentSRNDEventSpec v AM M α β) : ConvergentRNDEvent v AM M α β :=
  newAbstractConvergentFRNDEvent ev.toAbstractConvergentFRNDEventSpec

structure AbstractConvergentSRNDEventSpec' (v) [Preorder v] [WellFoundedLT v]
                             (AM) [Machine ACTX AM]
                             (M) [Machine CTX M]
                            [instSR: SRefinement AM M] (α)
           where

  event : ConvergentNDEvent v AM α Unit

  step_inv (m : M) (x : α):
    Machine.invariant m
    → event.guard (lift m) x
    → ∀ am', event.effect (lift m) x ((), am')
             → Machine.invariant (unlift m am')

@[simp]
def AbstractConvergentSRNDEventSpec'.toAbstractConvergentSRNDEventSpec [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (ev : AbstractConvergentSRNDEventSpec' v AM M α) : AbstractConvergentSRNDEventSpec v AM M α Unit :=
  {
    event := ev.event
    step_inv := fun m x Hinv Hgrd _ => ev.step_inv m x Hinv Hgrd
  }

@[simp]
def newAbstractConvergentSRNDEvent' [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (ev : AbstractConvergentSRNDEventSpec' v AM M α) : ConvergentRNDEvent v AM M α Unit :=
  newAbstractConvergentSRNDEvent ev.toAbstractConvergentSRNDEventSpec

structure AbstractConvergentSRNDEventSpec'' (v) [Preorder v] [WellFoundedLT v]
                             (AM) [Machine ACTX AM]
                             (M) [Machine CTX M]
                            [instSR: SRefinement AM M]
           where

  event : ConvergentNDEvent v AM Unit Unit

  step_inv (m : M):
    Machine.invariant m
    → event.guard (lift m) ()
    → ∀ am', event.effect (lift m) () ((), am')
             → Machine.invariant (unlift m am')

@[simp]
def AbstractConvergentSRNDEventSpec''.toAbstractConvergentSRNDEventSpec [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (ev : AbstractConvergentSRNDEventSpec'' v AM M) : AbstractConvergentSRNDEventSpec v AM M Unit Unit :=
  {
    event := ev.event
    step_inv := fun m _ Hinv Hgrd _ => ev.step_inv m Hinv Hgrd
  }

@[simp]
def newAbstractConvergentSRNDEvent'' [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (ev : AbstractConvergentSRNDEventSpec'' v AM M) : ConvergentRNDEvent v AM M Unit Unit :=
  newAbstractConvergentSRNDEvent ev.toAbstractConvergentSRNDEventSpec
