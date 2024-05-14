
/-
  Reuse of abstract events (functional refinement)
-/

import EventSystems.Refinement.Strong.Basic
import EventSystems.Refinement.Functional.Abstract

open Refinement
open FRefinement
open SRefinement

structure AbstractSREventSpec (AM) [Machine ACTX AM]
                             (M) [Machine CTX M]
                            [SRefinement AM M]
  {α β} (abstract : _Event AM α β)
          where

  step_inv (m : M) (x : α):
    Machine.invariant m
    → abstract.guard (lift m) x
    → Machine.invariant (unlift m (abstract.action (lift m) x).2)

@[simp]
def AbstractSREventSpec.toAbstractFREventSpec [Machine ACTX AM] [Machine CTX M] [instSR: SRefinement AM M]
  (abstract : OrdinaryEvent AM α β)
  (ev : AbstractSREventSpec AM M abstract.to_Event) : AbstractFREventSpec AM M abstract.to_Event :=
  {
    unlift := fun _ am' m _ => SRefinement.unlift m am'

    step_ref := fun m x => by
      simp
      intros Hinv Hgrd
      have Hlr := lift_ref (self:=instSR.toFRefinement) m Hinv
      have Hsafe := refine_safe (self:=instSR.toRefinement) (lift m) m Hinv Hlr
      have Hinv' := abstract.po.safety (lift m) x Hsafe Hgrd
      refine unlift_refine ?Hsafe Hinv Hinv'
      intros
      exact ev.step_inv m x Hinv Hgrd

    step_safe := fun m x => by
      simp
      intros Hinv Hgrd _
      exact ev.step_inv m x Hinv Hgrd
  }

@[simp]
def newAbstractSREvent [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (abs : OrdinaryEvent AM α β)
  (ev : AbstractSREventSpec AM M abs.to_Event) : OrdinaryREvent AM M α β :=
  newAbstractFREvent abs ev.toAbstractFREventSpec


@[simp]
def AbstractSREventSpec.toAbstractAnticipatedFREventSpec [Preorder v] [Machine ACTX AM] [Machine CTX M] [instSR: SRefinement AM M]
  (abstract : AnticipatedEvent v AM α β)
  (ev : AbstractSREventSpec AM M abstract.to_Event) : AbstractAnticipatedFREventSpec v AM M abstract :=
  {
    toAbstractFREventSpec := ev.toAbstractFREventSpec abstract.toOrdinaryEvent

    step_variant := fun m x => by
      simp
      intros Hinv Hgrd Hinv'
      have Hlr := lift_ref (self:=instSR.toFRefinement) m Hinv
      have Hsafe := refine_safe (self:=instSR.toRefinement) (lift m) m Hinv Hlr
      have Hni := abstract.po.nonIncreasing (lift m) x Hsafe Hgrd
      simp at Hni
      rw [lift_unlift] <;> assumption
  }

@[simp]
def newAbstractAnticipatedSREvent [Preorder v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (abs : AnticipatedEvent v AM α β)
  (ev : AbstractSREventSpec AM M abs.to_Event) : AnticipatedREvent v AM M α β :=
  newAbstractAnticipatedFREvent abs ev.toAbstractAnticipatedFREventSpec


@[simp]
def AbstractSREventSpec.toAbstractConvergentFREventSpec [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [instSR: SRefinement AM M]
  (abstract : ConvergentEvent v AM α β)
  (ev : AbstractSREventSpec AM M abstract.to_Event) : AbstractConvergentFREventSpec v AM M abstract :=
  {
    toAbstractAnticipatedFREventSpec := ev.toAbstractAnticipatedFREventSpec abstract.toAnticipatedEvent
  }

@[simp]
def newAbstractConvergentSREvent [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (abs : ConvergentEvent v AM α β)
  (ev : AbstractSREventSpec AM M abs.to_Event) : ConvergentREvent v AM M α β :=
  newAbstractConvergentFREvent abs ev.toAbstractConvergentFREventSpec
