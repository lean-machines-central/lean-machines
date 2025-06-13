
import LeanMachines.Event.Ordinary
import LeanMachines.Event.Convergent
import LeanMachines.Refinement.Relational.Convergent
import LeanMachines.Refinement.Relational.NonDet.Det.Basic
import LeanMachines.Refinement.Relational.NonDet.Det.Ordinary
import LeanMachines.NonDet.Convergent

/-!

## Convergent deterministic refined events

This module defines the construction of anticipated and
convergent events that deterministically refine a
non-deterministic abstract even.

-/

/-!
**TODO** Ajouter les smart constructors
-/


open Refinement

/-!
### Anticipated refined events
-/



-- class AnticipatedRDetEventPO (v) [Preorder v]  [Machine ACTX AM]
--   [instM:Machine CTX M] [instR: Refinement AM M]
--   (ev : Event M α β) (abs : NDEvent AM α' β')
--   [instSafeAbs : SafeNDEventPO abs kabs]
--   [instSafeEv : AnticipatedEventPO v ev kev]
--   {valid_kind : kev.canRefine? kabs = true}
--   where

--   nonIncreasing (m : M) (x : α):
--     Machine.invariant m
--     → (grd : ev.guard m x)
--     → let (_, m') := ev.action m x grd
--       variant m' ≤ variant m


structure AnticipatedRDetEvent (v) [Preorder v] (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: Refinement AM M]
  (α) (β) (α':=α) (β':=β) (abs : OrdinaryNDEvent AM α' β')
  extends AnticipatedEvent v M α β,
          OrdinaryRDetEvent AM M α β α' β' abs where


instance [Machine ACTX AM] [Machine CTX M] [instR : Refinement AM M] [Preorder v]
  (abs : OrdinaryNDEvent AM α' β') (ev : AnticipatedRDetEvent AM M (v := v) α β α' β' abs) :
    SafeRDetEventPO
      (ev.toEvent ) (abs.toNDEvent )
      (instSafeAbs := (instSafeNDEventPO_Ordinary abs))
      (instSafeEv := (instAnticipatedEventPO_AnticipatedEvent ev.toAnticipatedEvent).toSafeEventPO)
      (valid_kind := by simp)
  where
    lift_in := ev.lift_in
    lift_out := ev.lift_out
    strengthening := ev.strengthening
    simulation := ev.simulation


instance [Machine ACTX AM] [Machine CTX M] [instR : Refinement AM M] [Preorder v'] [Preorder v]
  (abs : AnticipatedNDEvent v' AM α' β') (ev : AnticipatedRDetEvent AM M (v := v) α β  α' β' abs.toOrdinaryNDEvent) :
    SafeRDetEventPO
      (ev.toEvent) (abs.toNDEvent)
      (instSafeAbs := (instSafeNDEventPO_Anticipated abs))
      (instSafeEv := (instAnticipatedEventPO_AnticipatedEvent ev.toAnticipatedEvent).toSafeEventPO)
      (valid_kind := by simp)
  where
    lift_in := ev.lift_in
    lift_out := ev.lift_out
    strengthening := ev.strengthening
    simulation := ev.simulation




@[simp]
def newAnticipatedFromOrdinaryRDetEvent [Machine ACTX AM] [Machine CTX M] [Refinement AM M] [Preorder v]
  (abs : OrdinaryNDEvent AM α' β')
  (ev: AnticipatedRDetEvent AM M α β (v := v) α' β' abs)
  : AnticipatedRDetEvent AM M α β (v := v) α' β' abs:= ev

def newAnticipatedFromAnticipatedRDetEvent [Machine ACTX AM] [Machine CTX M] [Refinement AM M] [Preorder v'] [Preorder v]
  (abs : AnticipatedNDEvent v' AM α' β')
  (ev: AnticipatedRDetEvent AM M  (α := α) (β := β) (v := v) α' β' abs.toOrdinaryNDEvent)
  : AnticipatedRDetEvent AM M  (α := α) (β := β) (v := v) α' β' abs.toOrdinaryNDEvent:= ev


/-!
### Convergent refined events
-/






structure ConvergentRDetEvent (v) [Preorder v] [WellFoundedLT v]
  (AM) [Machine ACTX AM] (M) [Machine CTX M] [instR: Refinement AM M]
  (α) (β) (α':=α) (β':=β) (abs : OrdinaryNDEvent AM α' β')
  extends ConvergentEvent v M α β,
          OrdinaryRDetEvent AM M α β α' β' abs where


instance [Machine ACTX AM] [Machine CTX M] [instR : Refinement AM M]
  [Preorder v] [WellFoundedLT v]
  (abs : OrdinaryNDEvent AM α' β') (ev : ConvergentRDetEvent AM M (v := v) α β α' β' abs) :
    SafeRDetEventPO
      (ev.toEvent ) (abs.toNDEvent )
      (instSafeAbs := (instSafeNDEventPO_Ordinary abs))
      (instSafeEv := (instConvergentEventPO_ConvergentEvent ev.toConvergentEvent).toSafeEventPO)
      (valid_kind := by simp)
  where
    lift_in := ev.lift_in
    lift_out := ev.lift_out
    strengthening := ev.strengthening
    simulation := ev.simulation

instance [Machine ACTX AM] [Machine CTX M] [instR : Refinement AM M]
  [Preorder v'] [Preorder v] [WellFoundedLT v]
  (abs : AnticipatedNDEvent v' AM α' β') (ev : ConvergentRDetEvent AM M (v := v) α β  α' β' abs.toOrdinaryNDEvent) :
    SafeRDetEventPO
      (ev.toEvent) (abs.toNDEvent)
      (instSafeAbs := (instSafeNDEventPO_Anticipated abs))
      (instSafeEv := (instConvergentEventPO_ConvergentEvent ev.toConvergentEvent).toSafeEventPO)
      (valid_kind := by simp)
  where
    lift_in := ev.lift_in
    lift_out := ev.lift_out
    strengthening := ev.strengthening
    simulation := ev.simulation

instance [Machine ACTX AM] [Machine CTX M] [instR : Refinement AM M]
  [Preorder v'] [Preorder v] [WellFoundedLT v] [WellFoundedLT v']
  (abs : ConvergentNDEvent v' AM α' β') (ev : ConvergentRDetEvent AM M (v := v) α β  α' β' abs.toOrdinaryNDEvent) :
    SafeRDetEventPO
      (ev.toEvent) (abs.toNDEvent)
      (instSafeAbs := (instSafeNDEventPO_Convergent abs))
      (instSafeEv := (instConvergentEventPO_ConvergentEvent ev.toConvergentEvent).toSafeEventPO)
      (valid_kind := by simp)
  where
    lift_in := ev.lift_in
    lift_out := ev.lift_out
    strengthening := ev.strengthening
    simulation := ev.simulation



@[simp]
def newConvergentFromOrdinaryRDetEvent [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
   [Preorder v] [WellFoundedLT v]
  (abs : OrdinaryNDEvent AM α' β')
  (ev: ConvergentRDetEvent AM M α β (v := v) α' β' abs)
  : ConvergentRDetEvent AM M α β (v := v) α' β' abs:= ev

def newConvergentFromAnticipatedRDetEvent [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
   [Preorder v'] [Preorder v] [WellFoundedLT v]
  (abs : AnticipatedNDEvent v' AM α' β')
  (ev: ConvergentRDetEvent AM M  (α := α) (β := β) (v := v) α' β' abs.toOrdinaryNDEvent)
  : ConvergentRDetEvent AM M  (α := α) (β := β) (v := v) α' β' abs.toOrdinaryNDEvent:= ev

def newConvergentFromConvergentRDetEvent [Machine ACTX AM] [Machine CTX M] [Refinement AM M]
   [Preorder v'] [Preorder v] [WellFoundedLT v]  [WellFoundedLT v']
  (abs : ConvergentNDEvent v' AM α' β')
  (ev: ConvergentRDetEvent AM M  (α := α) (β := β) (v := v) α' β' abs.toOrdinaryNDEvent)
  : ConvergentRDetEvent AM M  (α := α) (β := β) (v := v) α' β' abs.toOrdinaryNDEvent:= ev
