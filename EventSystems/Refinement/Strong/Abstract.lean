
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
                            [SRefinement AM M] (α) (β)
          where

  event : OrdinaryEvent AM α β

  step_inv (m : M) (x : α):
    Machine.invariant m
    → event.guard (lift m) x
    → Machine.invariant (unlift m (event.action (lift m) x).2)

@[simp]
def AbstractSREventSpec.toAbstractFREventSpec [Machine ACTX AM] [Machine CTX M] [instSR: SRefinement AM M]
  (ev : AbstractSREventSpec AM M α β) : AbstractFREventSpec AM M α β :=
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
  }
