
import EventSystems.Refinement.Strong.NonDet.Basic
import EventSystems.Refinement.Functional.NonDet.Abstract

open Refinement
open FRefinement
open SRefinement

structure AbstractSRNDEventSpec (AM) [Machine ACTX AM]
                             (M) [Machine CTX M]
                            [instSR: SRefinement AM M]
  {α β} (abstract : _NDEvent AM α β)
      where

  step_inv (m : M) (x : α):
    Machine.invariant m
    → abstract.guard (lift m) x
    → ∀ y, ∀ am', abstract.effect (lift m) x (y, am')
                  → Machine.invariant (unlift m am')

@[simp]
def AbstractSRNDEventSpec.toAbstractFRNDEventSpec  [Machine ACTX AM] [Machine CTX M] [instSR: SRefinement AM M]
  (abstract : OrdinaryNDEvent AM α β)
  (ev : AbstractSRNDEventSpec AM M abstract.to_NDEvent) : AbstractFRNDEventSpec AM M abstract.to_NDEvent :=
  {
    unlift := fun _ am' m _ => SRefinement.unlift m am'

    step_ref := fun m x => by
      simp
      intros Hinv Hgrd y am' Heff
      have Hlr := lift_ref (self:=instSR.toFRefinement) m Hinv
      have Hsafe := refine_safe (self:=instSR.toRefinement) (lift m) m Hinv Hlr
      have Hinv' := abstract.po.safety (lift m) x Hsafe Hgrd y am' Heff
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
  (abs : OrdinaryNDEvent AM α β)
  (ev : AbstractSRNDEventSpec AM M abs.to_NDEvent) : OrdinaryRNDEvent AM M α β :=
  newAbstractFRNDEvent abs ev.toAbstractFRNDEventSpec

@[simp]
def newAbstractAnticipatedSRNDEvent [Preorder v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (abs : AnticipatedNDEvent v AM α β)
  (ev : AbstractSRNDEventSpec AM M abs.to_NDEvent) : AnticipatedRNDEvent v AM M α β :=
  newAbstractAnticipatedFRNDEvent abs (ev.toAbstractFRNDEventSpec abs.toOrdinaryNDEvent)

@[simp]
def newAbstractConvergentSRNDEvent [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (abs : ConvergentNDEvent v AM α β) (ev : AbstractSRNDEventSpec AM M abs.to_NDEvent) : ConvergentRNDEvent v AM M α β :=
  newAbstractConvergentFRNDEvent abs (ev.toAbstractFRNDEventSpec abs.toAnticipatedNDEvent.toOrdinaryNDEvent)
