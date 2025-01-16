
/-
  Reuse of abstract events (functional refinement)
-/

import LeanMachines.Refinement.Strong.Basic
import LeanMachines.Refinement.Functional.Basic
import LeanMachines.Refinement.Functional.Abstract

open Refinement
open FRefinement
open SRefinement

structure AbstractSREventSpec (AM) [@Machine ACTX AM]
                             (M) [@Machine CTX M]
                            [SRefinement AM M]
  {α β} (abstract : OrdinaryEvent AM α β)
          where

  step_inv (m : M) (x : α):
    Machine.invariant m
    → (agrd : abstract.guard (lift m) x)
    → Machine.invariant (unlift m (abstract.action (lift m) x agrd).2)

@[simp]
def AbstractSREventSpec.toAbstractFREventSpec [@Machine ACTX AM] [@Machine CTX M] [instSR: SRefinement AM M]
  (abstract : OrdinaryEvent AM α β)
  (ev : AbstractSREventSpec AM M abstract) : AbstractFREventSpec AM M abstract :=
  {
    unlift := fun _ am' m _ => SRefinement.unlift m am'

    step_ref := fun m x => by
      simp
      intros Hinv Hgrd
      simp [refine]
      rw [lift_unlift]
      · assumption
      have Hlr := lift_ref (AM:= AM) (M:=M) m Hinv
      have Hsafe := refine_safe (AM:= AM) (M:=M) (self:=instRefinementOfFRefinement) (lift m) m Hinv Hlr
      have Hinv' := abstract.po.safety (lift m) x Hsafe Hgrd
      assumption

    step_safe := fun m x => by
      simp
      intros Hinv Hgrd _
      exact ev.step_inv m x Hinv Hgrd
  }

@[simp]
def newAbstractSREvent [@Machine ACTX AM] [@Machine CTX M] [SRefinement AM M]
  (abs : OrdinaryEvent AM α β)
  (ev : AbstractSREventSpec AM M abs) : OrdinaryREvent AM M α β :=
  newAbstractFREvent abs ev.toAbstractFREventSpec

@[simp]
def newAbstractSREvent' [@Machine ACTX AM] [@Machine CTX M] [SRefinement AM M]
  (abs : OrdinaryEvent AM α Unit)
  (ev : AbstractSREventSpec AM M abs) : OrdinaryREvent AM M α Unit :=
  newAbstractFREvent abs ev.toAbstractFREventSpec

structure AbstractSREventSpec'' (AM) [@Machine ACTX AM]
                             (M) [@Machine CTX M]
                            [SRefinement AM M]
  (abstract : OrdinaryEvent AM Unit Unit)
          where

  step_inv (m : M):
    Machine.invariant m
    → (agrd : abstract.guard (lift m) ())
    → Machine.invariant (unlift m (abstract.action (lift m) x agrd).2)

@[simp]
def AbstractSREventSpec''.toAbstractSREventSpec [@Machine ACTX AM] [@Machine CTX M] [SRefinement AM M]
  (abstract : OrdinaryEvent AM Unit Unit)
  (ev : AbstractSREventSpec'' AM M abstract) : AbstractSREventSpec AM M abstract :=
  {
    step_inv := fun m _ => ev.step_inv m
  }

@[simp]
def newAbstractSREvent'' [@Machine ACTX AM] [@Machine CTX M] [SRefinement AM M]
  (abs : OrdinaryEvent AM Unit Unit)
  (ev : AbstractSREventSpec'' AM M abs) : OrdinaryREvent AM M Unit Unit :=
  newAbstractSREvent abs ev.toAbstractSREventSpec

structure AbstractInitSREventSpec (AM) [@Machine ACTX AM]
                             (M) [@Machine CTX M]
                            [instSR: SRefinement AM M]
  {α β} (abstract : InitEvent AM α β)
          where

  step_inv (x : α):
    (agrd : abstract.guard x)
    → Machine.invariant (unlift (self:=instSR) default (abstract.init x agrd).2)

@[simp]
def AbstractInitSREventSpec.toAbstractInitFREventSpec [@Machine ACTX AM] [@Machine CTX M] [instSR: SRefinement AM M]
  (abstract : InitEvent AM α β)
  (ev : AbstractInitSREventSpec AM M abstract) : AbstractInitFREventSpec AM M abstract :=
  {
    unlift := fun _ am' m _ => SRefinement.unlift m am'

    step_ref := fun x => by
      simp
      intros Hgrd
      have Hainv := abstract.po.safety x Hgrd
      have Hsi := ev.step_inv x Hgrd
      have Href := lift_ref (AM:=AM) (unlift default (abstract.init x Hgrd).2) Hsi
      have Hlu := lu_default (self:=instSR) (abstract.init x Hgrd).2 Hainv
      rw [Hlu] at Href
      assumption

    step_safe := fun x => by
      simp
      intros Hgrd _
      apply ev.step_inv x Hgrd

  }

@[simp]
def newAbstractInitSREvent [@Machine ACTX AM] [@Machine CTX M] [SRefinement AM M]
  (abs : InitEvent AM α β)
  (ev : AbstractInitSREventSpec AM M abs) : InitREvent AM M α β :=
  newAbstractInitFREvent abs ev.toAbstractInitFREventSpec

@[simp]
def newAbstractInitSREvent' [@Machine ACTX AM] [@Machine CTX M] [SRefinement AM M]
  (abs : InitEvent AM α Unit)
  (ev : AbstractInitSREventSpec AM M abs) : InitREvent AM M α Unit :=
  newAbstractInitFREvent abs ev.toAbstractInitFREventSpec

structure AbstractInitSREventSpec'' (AM) [@Machine ACTX AM]
                             (M) [@Machine CTX M]
                            [instSR: SRefinement AM M]
  (abstract : InitEvent AM Unit Unit)
          where

  step_inv:
    (agrd : abstract.guard ())
    → Machine.invariant (unlift (self:=instSR) default (abstract.init () agrd).2)

@[simp]
def AbstractInitSREventSpec''.toAbstractInitSREventSpec [@Machine ACTX AM] [@Machine CTX M] [SRefinement AM M]
  (abstract : InitEvent AM Unit Unit)
  (ev : AbstractInitSREventSpec'' AM M abstract) : AbstractInitSREventSpec AM M abstract :=
  {
     step_inv := fun _ => ev.step_inv
  }

@[simp]
def newAbstractInitSREvent'' [@Machine ACTX AM] [@Machine CTX M] [SRefinement AM M]
  (abs : InitEvent AM Unit Unit)
  (ev : AbstractInitSREventSpec'' AM M abs) : InitREvent AM M Unit Unit :=
  newAbstractInitSREvent abs ev.toAbstractInitSREventSpec

@[simp]
def AbstractSREventSpec.toAbstractAnticipatedFREventSpec [Preorder v] [@Machine ACTX AM] [@Machine CTX M] [instSR: SRefinement AM M]
  (abstract : AnticipatedEvent v AM α β)
  (ev : AbstractSREventSpec AM M abstract.toOrdinaryEvent) : AbstractAnticipatedFREventSpec v AM M abstract :=
  {
    toAbstractFREventSpec := ev.toAbstractFREventSpec abstract.toOrdinaryEvent

    step_variant := fun m x => by
      simp
      intros Hinv Hgrd Hinv'
      have Hlr := lift_ref (AM:=AM) m Hinv
      have Hsafe := refine_safe (self:=instRefinementOfFRefinement) (lift m) m Hinv Hlr
      have Hni := abstract.po.nonIncreasing (lift m) x Hsafe Hgrd
      simp at Hni
      rw [lift_unlift] <;> assumption
  }

@[simp]
def newAbstractAnticipatedSREvent [Preorder v] [@Machine ACTX AM] [@Machine CTX M] [SRefinement AM M]
  (abs : AnticipatedEvent v AM α β)
  (ev : AbstractSREventSpec AM M abs.toOrdinaryEvent) : AnticipatedREvent v AM M α β :=
  newAbstractAnticipatedFREvent abs ev.toAbstractAnticipatedFREventSpec

@[simp]
def newAbstractAnticipatedSREvent' [Preorder v] [@Machine ACTX AM] [@Machine CTX M] [SRefinement AM M]
  (abs : AnticipatedEvent v AM α Unit)
  (ev : AbstractSREventSpec AM M abs.toOrdinaryEvent) : AnticipatedREvent v AM M α Unit :=
  newAbstractAnticipatedFREvent abs ev.toAbstractAnticipatedFREventSpec

@[simp]
def newAbstractAnticipatedSREvent'' [Preorder v] [@Machine ACTX AM] [@Machine CTX M] [SRefinement AM M]
  (abs : AnticipatedEvent v AM Unit Unit)
  (ev : AbstractSREventSpec'' AM M abs.toOrdinaryEvent) : AnticipatedREvent v AM M Unit Unit :=
  newAbstractAnticipatedSREvent abs ev.toAbstractSREventSpec

@[simp]
def newAbstractConvergentSREvent [Preorder v] [WellFoundedLT v] [@Machine ACTX AM] [@Machine CTX M] [SRefinement AM M]
  (abs : ConvergentEvent v AM α β)
  (ev : AbstractSREventSpec AM M abs.toOrdinaryEvent) : ConvergentREvent v AM M α β :=
  newAbstractConvergentFREvent abs (ev.toAbstractAnticipatedFREventSpec abs.toAnticipatedEvent)

@[simp]
def newAbstractConvergentSREvent' [Preorder v] [WellFoundedLT v] [@Machine ACTX AM] [@Machine CTX M] [SRefinement AM M]
  (abs : ConvergentEvent v AM α Unit)
  (ev : AbstractSREventSpec AM M abs.toOrdinaryEvent) : ConvergentREvent v AM M α Unit :=
  newAbstractConvergentFREvent abs (ev.toAbstractAnticipatedFREventSpec abs.toAnticipatedEvent)

@[simp]
def newAbstractConvergentSREvent'' [Preorder v] [WellFoundedLT v] [@Machine ACTX AM] [@Machine CTX M] [SRefinement AM M]
  (abs : ConvergentEvent v AM Unit Unit)
  (ev : AbstractSREventSpec'' AM M abs.toOrdinaryEvent) : ConvergentREvent v AM M Unit Unit :=
  newAbstractConvergentSREvent abs ev.toAbstractSREventSpec
