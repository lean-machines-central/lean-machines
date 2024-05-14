
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

structure AbstractAnticipatedSREventSpec (v) [Preorder v]
                             (AM) [Machine ACTX AM]
                             (M) [Machine CTX M]
                             [SRefinement AM M] (α) (β)
          where

  event : AnticipatedEvent v AM α β

  step_inv (m : M) (x : α):
    Machine.invariant m
    → event.guard (lift m) x
    → Machine.invariant (unlift m (event.action (lift m) x).2)

@[simp]
def AbstractAnticipatedSREventSpec.toAbstractAnticipatedFREventSpec [Preorder v] [Machine ACTX AM] [Machine CTX M] [instSR: SRefinement AM M]
  (ev : AbstractAnticipatedSREventSpec v AM M α β) : AbstractAnticipatedFREventSpec v AM M α β :=
  {
    event := ev.event
    unlift := fun _ am' m _ => SRefinement.unlift m am'

    step_ref := fun m x => by
      simp
      intros Hinv Hgrd
      have Hlr := lift_ref (self:=instSR.toFRefinement) m Hinv
      have Hsafe := refine_safe (self:=instSR.toRefinement) (lift m) m Hinv Hlr
      have Hinv' := ev.event.po.safety (lift m) x Hsafe Hgrd
      refine unlift_refine ?Hsafe Hinv Hinv'
      intros
      exact ev.step_inv m x Hinv Hgrd

    step_safe := fun m x => by
      simp
      intros Hinv Hgrd _
      exact ev.step_inv m x Hinv Hgrd

    step_variant := fun m x => by
      simp
      intros Hinv Hgrd Hinv'
      have Hlr := lift_ref (self:=instSR.toFRefinement) m Hinv
      have Hsafe := refine_safe (self:=instSR.toRefinement) (lift m) m Hinv Hlr
      have Hni := ev.event.po.nonIncreasing (lift m) x Hsafe Hgrd
      simp at Hni
      rw [lift_unlift] <;> assumption
  }

@[simp]
def newAbstractAnticipatedSREvent [Preorder v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (abs : AbstractAnticipatedSREventSpec v AM M α β) : AnticipatedREvent v AM M α β :=
  newAbstractAnticipatedFREvent abs.toAbstractAnticipatedFREventSpec

structure AbstractAnticipatedSREventSpec' (v) [Preorder v]
                             (AM) [Machine ACTX AM]
                             (M) [Machine CTX M]
                            [SRefinement AM M] (α)
    extends AbstractAnticipatedSREventSpec v AM M α Unit where

@[simp]
def newAbstractAnticipatedSREvent' [Preorder v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (abs : AbstractAnticipatedSREventSpec' v AM M α) : AnticipatedREvent v AM M α Unit :=
  newAbstractAnticipatedFREvent abs.toAbstractAnticipatedFREventSpec

structure AbstractAnticipatedSREventSpec'' (v) [Preorder v]
                                (AM) [Machine ACTX AM]
                                (M) [Machine CTX M]
                                [SRefinement AM M]
          where

  event : AnticipatedEvent v AM Unit Unit

  step_inv (m : M):
    Machine.invariant m
    → event.guard (lift m) ()
    → Machine.invariant (unlift m (event.action (lift m) ()).2)

@[simp]
def AbstractAnticipatedSREventSpec''.toAbstractAnticipatedSREventSpec  [Preorder v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (abs : AbstractAnticipatedSREventSpec'' v AM M) : AbstractAnticipatedSREventSpec v AM M Unit Unit :=
  {
    event := abs.event
    step_inv := fun m _ => abs.step_inv m
  }

@[simp]
def newAbstractAnticipatedSREvent'' [Preorder v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (abs : AbstractAnticipatedSREventSpec'' v AM M) : AnticipatedREvent v AM M Unit Unit :=
  newAbstractAnticipatedSREvent abs.toAbstractAnticipatedSREventSpec

structure AbstractConvergentSREventSpec (v) [Preorder v] [WellFoundedLT v]
                             (AM) [Machine ACTX AM]
                             (M) [Machine CTX M]
                             [SRefinement AM M] (α) (β)
          where

  event : ConvergentEvent v AM α β

  step_inv (m : M) (x : α):
    Machine.invariant m
    → event.guard (lift m) x
    → Machine.invariant (unlift m (event.action (lift m) x).2)

@[simp]
def AbstractConvergentSREventSpec.toAbstractConvergentFREventSpec [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [instSR: SRefinement AM M]
  (ev : AbstractConvergentSREventSpec v AM M α β) : AbstractConvergentFREventSpec v AM M α β :=
  {
    event := ev.event
    unlift := fun _ am' m _ => SRefinement.unlift m am'

    step_ref := fun m x => by
      simp
      intros Hinv Hgrd
      have Hlr := lift_ref (self:=instSR.toFRefinement) m Hinv
      have Hsafe := refine_safe (self:=instSR.toRefinement) (lift m) m Hinv Hlr
      have Hinv' := ev.event.po.safety (lift m) x Hsafe Hgrd
      refine unlift_refine ?Hsafe Hinv Hinv'
      intros
      exact ev.step_inv m x Hinv Hgrd

    step_safe := fun m x => by
      simp
      intros Hinv Hgrd _
      exact ev.step_inv m x Hinv Hgrd

    step_variant := fun m x => by
      simp
      intros Hinv Hgrd Hinv'
      have Hlr := lift_ref (self:=instSR.toFRefinement) m Hinv
      have Hsafe := refine_safe (self:=instSR.toRefinement) (lift m) m Hinv Hlr
      have Hni := ev.event.po.nonIncreasing (lift m) x Hsafe Hgrd
      simp at Hni
      rw [lift_unlift] <;> assumption
  }

@[simp]
def newAbstractConvergentSREvent [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (abs : AbstractConvergentSREventSpec v AM M α β) : ConvergentREvent v AM M α β :=
  newAbstractConvergentFREvent abs.toAbstractConvergentFREventSpec

structure AbstractConvergentSREventSpec' (v) [Preorder v] [WellFoundedLT v]
                             (AM) [Machine ACTX AM]
                             (M) [Machine CTX M]
                            [SRefinement AM M] (α)
    extends AbstractConvergentSREventSpec v AM M α Unit where

@[simp]
def newAbstractConvergentSREvent' [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (abs : AbstractConvergentSREventSpec' v AM M α) : ConvergentREvent v AM M α Unit :=
  newAbstractConvergentFREvent abs.toAbstractConvergentFREventSpec

structure AbstractConvergentSREventSpec'' (v) [Preorder v] [WellFoundedLT v]
                                (AM) [Machine ACTX AM]
                                (M) [Machine CTX M]
                                [SRefinement AM M]
          where

  event : ConvergentEvent v AM Unit Unit

  step_inv (m : M):
    Machine.invariant m
    → event.guard (lift m) ()
    → Machine.invariant (unlift m (event.action (lift m) ()).2)

@[simp]
def AbstractConvergentSREventSpec''.toAbstractConvergentSREventSpec  [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (abs : AbstractConvergentSREventSpec'' v AM M) : AbstractConvergentSREventSpec v AM M Unit Unit :=
  {
    event := abs.event
    step_inv := fun m _ => abs.step_inv m
  }

@[simp]
def newAbstractConvergentSREvent'' [Preorder v] [WellFoundedLT v] [Machine ACTX AM] [Machine CTX M] [SRefinement AM M]
  (abs : AbstractConvergentSREventSpec'' v AM M) : ConvergentREvent v AM M Unit Unit :=
  newAbstractConvergentSREvent abs.toAbstractConvergentSREventSpec
